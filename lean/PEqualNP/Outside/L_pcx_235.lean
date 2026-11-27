import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_235

abbrev Lit (W : Type) := PEqualNP.ProofComplexity.Literal W
abbrev Cl (W : Type) := PEqualNP.ProofComplexity.Clause W
abbrev Vis (n w : ℕ) := Sum (Fin n) (Fin n × (Fin (w + 1) → Bool))

def negL {W : Type} (l : Lit W) : Lit W := PEqualNP.Search.negLit l

def Accepts (n w : ℕ) (hn : 0 < n) (a : Vis n w → Bool) : Prop :=
  ∀ i : Fin n, a (Sum.inr (i, fun j : Fin (w + 1) =>
    a (Sum.inl ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩))) = true

def upStep {W : Type} (F : Finset (Cl W)) (S : Set (Lit W)) : Set (Lit W) :=
  S ∪ {l | ∃ D ∈ F, l ∈ D ∧ ∀ other ∈ D, other ≠ l → negL other ∈ S}

def seedOf {V M : Type} (ρ : V → Option Bool) : Set (Lit (Sum V M)) :=
  {l | ∃ v : V, l.1 = Sum.inl v ∧ ρ v = some l.2}

def Completion (n w : ℕ) (hn : 0 < n) (ρ : Vis n w → Option Bool) (a : Vis n w → Bool) : Prop :=
  Accepts n w hn a ∧ ∀ (v : Vis n w) (b : Bool), ρ v = some b → a v = b

lemma negL_negL {W : Type} (l : Lit W) : negL (negL l) = l := by
  cases l with
  | mk v b =>
    cases b <;> rfl

lemma negL_fst {W : Type} (l : Lit W) : (negL l).1 = l.1 := rfl

lemma negL_snd {W : Type} (l : Lit W) : (negL l).2 = !l.2 := rfl

lemma negL_eq_iff {W : Type} (a b : Lit W) : negL a = b ↔ a = negL b := by
  constructor
  · intro h; rw [← h, negL_negL]
  · intro h; rw [h, negL_negL]

lemma subset_upStep {W : Type} (F : Finset (Cl W)) (S : Set (Lit W)) : S ⊆ upStep F S :=
  Set.subset_union_left

lemma upStep_mono {W : Type} {F1 F2 : Finset (Cl W)} {S1 S2 : Set (Lit W)}
    (hF : F1 ⊆ F2) (hS : S1 ⊆ S2) : upStep F1 S1 ⊆ upStep F2 S2 := by
  intro l hl
  rcases hl with hl | ⟨D, hD, hlD, hother⟩
  · exact Or.inl (hS hl)
  · exact Or.inr ⟨D, hF hD, hlD, fun o ho hne => hS (hother o ho hne)⟩

lemma upStep_iter_mono {W : Type} {F1 F2 : Finset (Cl W)} {S1 S2 : Set (Lit W)}
    (hF : F1 ⊆ F2) (hS : S1 ⊆ S2) : ∀ k : ℕ, (upStep F1)^[k] S1 ⊆ (upStep F2)^[k] S2
  | 0 => hS
  | k + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact upStep_mono hF (upStep_iter_mono hF hS k)

lemma upStep_iter_le {W : Type} (F : Finset (Cl W)) (S : Set (Lit W)) {k1 k2 : ℕ}
    (h : k1 ≤ k2) : (upStep F)^[k1] S ⊆ (upStep F)^[k2] S := by
  induction h with
  | refl => exact Set.Subset.rfl
  | @step m _ ih =>
    rw [Function.iterate_succ_apply']
    exact Set.Subset.trans ih (subset_upStep F _)

lemma upStep_sound {W : Type} {F : Finset (Cl W)} {α : W → Bool}
    (hF : PEqualNP.ProofComplexity.Satisfies α (↑F : Set (Cl W))) {S : Set (Lit W)}
    (hS : ∀ l ∈ S, α l.1 = l.2) : ∀ l ∈ upStep F S, α l.1 = l.2 := by
  intro l hl
  rcases hl with hl | ⟨D, hD, hlD, hother⟩
  · exact hS l hl
  · obtain ⟨u, huD, hu⟩ := hF D hD
    by_cases hEq : u = l
    · simpa [hEq] using hu
    · have hneg := hS (negL u) (hother u huD hEq)
      simp only [negL_fst, negL_snd] at hneg
      rw [hu] at hneg
      cases u.2 <;> simp at hneg

lemma upStep_iter_sound {W : Type} {F : Finset (Cl W)} {α : W → Bool}
    (hF : PEqualNP.ProofComplexity.Satisfies α (↑F : Set (Cl W))) {S : Set (Lit W)}
    (hS : ∀ l ∈ S, α l.1 = l.2) : ∀ k : ℕ, ∀ l ∈ (upStep F)^[k] S, α l.1 = l.2
  | 0 => hS
  | k + 1 => by
    rw [Function.iterate_succ_apply']
    exact upStep_sound hF (upStep_iter_sound hF hS k)

lemma seedOf_sound {V M : Type} {ρ : V → Option Bool} {a : V → Bool} {aux : M → Bool}
    (hρ : ∀ (v : V) (b : Bool), ρ v = some b → a v = b) :
    ∀ l ∈ (seedOf ρ : Set (Lit (Sum V M))), Sum.elim a aux l.1 = l.2 := by
  intro l ⟨v, hv, hrv⟩
  rw [hv]
  exact hρ v l.2 hrv

lemma enc_conflict_sound {n w d m : ℕ} {hn : 0 < n}
    {F : Finset (Cl (Sum (Vis n w) (Fin m)))}
    (hsat : ∀ total : Vis n w → Bool, Accepts n w hn total →
      ∃ aux : Fin m → Bool, PEqualNP.ProofComplexity.Satisfies (Sum.elim total aux) (↑F : Set _))
    {ρ : Vis n w → Option Bool}
    (hcomp : ∃ a : Vis n w → Bool, Completion n w hn ρ a) :
    ¬ ∃ D ∈ F, ∀ l ∈ D, negL l ∈ (upStep F)^[d] (seedOf ρ) := by
  rintro ⟨D, hD, hfalse⟩
  obtain ⟨a, ha, hρ⟩ := hcomp
  obtain ⟨aux, haux⟩ := hsat a ha
  have hK := upStep_iter_sound haux (seedOf_sound (aux := aux) hρ) d
  obtain ⟨l, hlD, hl⟩ := haux D hD
  have hneg := hK (negL l) (hfalse l hlD)
  simp only [negL_fst, negL_snd] at hneg
  rw [hl] at hneg
  cases l.2 <;> simp at hneg

lemma enc_force_sound {n w d m : ℕ} {hn : 0 < n}
    {F : Finset (Cl (Sum (Vis n w) (Fin m)))}
    (hsat : ∀ total : Vis n w → Bool, Accepts n w hn total →
      ∃ aux : Fin m → Bool, PEqualNP.ProofComplexity.Satisfies (Sum.elim total aux) (↑F : Set _))
    {ρ : Vis n w → Option Bool} {v : Vis n w} {b : Bool}
    (hmem : (Sum.inl v, b) ∈ (upStep F)^[d] (seedOf ρ)) :
    ∀ a : Vis n w → Bool, Completion n w hn ρ a → a v = b := by
  intro a ⟨ha, hρ⟩
  obtain ⟨aux, haux⟩ := hsat a ha
  have hK := upStep_iter_sound haux (seedOf_sound (aux := aux) hρ) d
  simpa using hK (Sum.inl v, b) hmem

lemma upStep_support {W : Type} [DecidableEq W] {F : Finset (Cl W)}
    (hcard : ∀ D ∈ F, D.card ≤ 3) (S : Set (Lit W)) :
    ∀ k : ℕ, ∀ l ∈ (upStep F)^[k] S,
      ∃ T : Finset (Lit W), (∀ x ∈ T, x ∈ S) ∧ T.card ≤ 2 ^ k ∧
        l ∈ (upStep F)^[k] (↑T : Set (Lit W))
  | 0, l, hl => by
    refine ⟨{l}, ?_, by simp, by simp⟩
    intro x hx
    simp only [Finset.mem_singleton] at hx
    rwa [hx]
  | k + 1, l, hl => by
    rw [Function.iterate_succ_apply'] at hl
    rcases hl with hl | ⟨D, hD, hlD, hother⟩
    · obtain ⟨T, hTS, hTcard, hlT⟩ := upStep_support hcard S k l hl
      refine ⟨T, hTS, hTcard.trans (Nat.pow_le_pow_right (by omega) (Nat.le_succ k)), ?_⟩
      rw [Function.iterate_succ_apply']
      exact Or.inl hlT
    · let E := D.erase l
      have hEc : E.card ≤ 2 := by
        have h1 := hcard D hD
        have h2 : E.card + 1 = D.card := Finset.card_erase_add_one hlD
        omega
      have hElen : E.toList.length ≤ 2 := by simpa [Finset.length_toList] using hEc
      match hL : E.toList with
      | [] =>
        refine ⟨∅, by simp, by simp, ?_⟩
        rw [Function.iterate_succ_apply']
        refine Or.inr ⟨D, hD, hlD, ?_⟩
        intro o ho hne
        have hoE : o ∈ E := Finset.mem_erase.2 ⟨hne, ho⟩
        have : o ∈ E.toList := Finset.mem_toList.2 hoE
        rw [hL] at this
        simp at this
      | [u] =>
        have huE : u ∈ E := Finset.mem_toList.1 (by rw [hL]; simp)
        have hu : negL u ∈ (upStep F)^[k] S :=
          hother u (Finset.mem_of_mem_erase huE) (Finset.ne_of_mem_erase huE)
        obtain ⟨T, hTS, hTcard, huT⟩ := upStep_support hcard S k (negL u) hu
        refine ⟨T, hTS, hTcard.trans (Nat.pow_le_pow_right (by omega) (Nat.le_succ k)), ?_⟩
        rw [Function.iterate_succ_apply']
        refine Or.inr ⟨D, hD, hlD, ?_⟩
        intro o ho hne
        have hoE : o ∈ E.toList := Finset.mem_toList.2 (Finset.mem_erase.2 ⟨hne, ho⟩)
        rw [hL] at hoE
        simp only [List.mem_singleton] at hoE
        rwa [hoE]
      | [u, v] =>
        have huE : u ∈ E := Finset.mem_toList.1 (by rw [hL]; simp)
        have hvE : v ∈ E := Finset.mem_toList.1 (by rw [hL]; simp)
        have hu : negL u ∈ (upStep F)^[k] S :=
          hother u (Finset.mem_of_mem_erase huE) (Finset.ne_of_mem_erase huE)
        have hv : negL v ∈ (upStep F)^[k] S :=
          hother v (Finset.mem_of_mem_erase hvE) (Finset.ne_of_mem_erase hvE)
        obtain ⟨T1, hT1S, hT1c, huT1⟩ := upStep_support hcard S k (negL u) hu
        obtain ⟨T2, hT2S, hT2c, hvT2⟩ := upStep_support hcard S k (negL v) hv
        refine ⟨T1 ∪ T2, ?_, ?_, ?_⟩
        · intro x hx
          rcases Finset.mem_union.1 hx with hx | hx
          · exact hT1S x hx
          · exact hT2S x hx
        · have h1 := Finset.card_union_le T1 T2
          have h2 : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
          omega
        · rw [Function.iterate_succ_apply']
          refine Or.inr ⟨D, hD, hlD, ?_⟩
          intro o ho hne
          have hoE : o ∈ E.toList := Finset.mem_toList.2 (Finset.mem_erase.2 ⟨hne, ho⟩)
          rw [hL] at hoE
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hoE
          rcases hoE with rfl | rfl
          · exact upStep_iter_mono Finset.Subset.rfl
              (by intro x hx; exact Finset.mem_coe.2 (Finset.mem_union_left T2 (Finset.mem_coe.1 hx))) k huT1
          · exact upStep_iter_mono Finset.Subset.rfl
              (by intro x hx; exact Finset.mem_coe.2 (Finset.mem_union_right T1 (Finset.mem_coe.1 hx))) k hvT2
      | _ :: _ :: _ :: _ =>
        rw [hL] at hElen
        simp at hElen

lemma bool_eq_not_of_ne {a b : Bool} (h : a ≠ b) : b = !a := by
  cases a <;> cases b <;> simp_all

lemma lower_bound_w0 {n d m : ℕ} (hn : 0 < n)
    (F : Finset (Cl (Sum (Vis n 0) (Fin m))))
    (hforce : ∀ ρ : Vis n 0 → Option Bool,
      (∃ a : Vis n 0 → Bool, Completion n 0 hn ρ a) →
      ∀ v : Vis n 0, ∀ b : Bool,
        (∀ a : Vis n 0 → Bool, Completion n 0 hn ρ a → a v = b) ↔
        (Sum.inl v, b) ∈ (upStep F)^[d] (seedOf ρ)) :
    1 ≤ d := by
  classical
  by_contra hd
  have hd0 : d = 0 := by omega
  subst hd0
  let i0 : Fin n := ⟨0, hn⟩
  let ρ : Vis n 0 → Option Bool := fun v =>
    if v = Sum.inl i0 then some true else none
  have hcomp : ∃ a : Vis n 0 → Bool, Completion n 0 hn ρ a := by
    refine ⟨fun _ => true, ?_, ?_⟩
    · intro i; rfl
    · intro v b hrv
      by_cases hv : v = Sum.inl i0
      · simp [ρ, hv] at hrv; exact hrv.symm
      · simp [ρ, hv] at hrv
  let vtarget : Vis n 0 := Sum.inr (i0, fun _ => true)
  have hforced : ∀ a : Vis n 0 → Bool, Completion n 0 hn ρ a → a vtarget = true := by
    intro a ⟨ha, hρ⟩
    have hx0 : a (Sum.inl i0) = true := hρ (Sum.inl i0) true (by simp [ρ])
    have hai := ha i0
    have hfun : (fun j : Fin 1 => a (Sum.inl ⟨(i0.val + j.val) % n, Nat.mod_lt _ hn⟩)) =
        (fun _ : Fin 1 => true) := by
      funext j
      have hj0 : j.val = 0 := by omega
      have hidx : (⟨(i0.val + j.val) % n, Nat.mod_lt _ hn⟩ : Fin n) = i0 := by
        apply Fin.ext; simp [i0]
      rw [hidx, hx0]
    rw [hfun] at hai
    exact hai
  have hmem := (hforce ρ hcomp vtarget true).1 hforced
  simp only [Function.iterate_zero, id_eq, seedOf] at hmem
  rcases hmem with ⟨v, hv, hrv⟩
  have hveq : v = vtarget := Sum.inl.inj hv.symm
  subst hveq
  simp [ρ, vtarget] at hrv

def isTwist (n : ℕ) (i : Fin n) (t : Fin 2 → Bool) : Bool :=
  if i.val + 1 < n then (t 0 != t 1) else (t 0 == t 1)

def mkBad (n : ℕ) (i : Fin n) (b : Bool) : Vis n 1 :=
  Sum.inr (i, fun j : Fin 2 => if j.val = 0 then b else if i.val + 1 < n then !b else b)

def twistRho (n : ℕ) : Vis n 1 → Option Bool
  | Sum.inl _ => none
  | Sum.inr (i, t) => if isTwist n i t then some false else none

lemma mkBad_injective (n : ℕ) : Function.Injective (fun p : Fin n × Bool => mkBad n p.1 p.2) := by
  rintro ⟨i1, b1⟩ ⟨i2, b2⟩ h
  simp only [mkBad, Sum.inr.injEq, Prod.mk.injEq] at h
  rcases h with ⟨rfl, ht⟩
  have h0 := congrFun ht 0
  simp at h0
  exact Prod.ext rfl h0

lemma twistRho_eq_some_iff (n : ℕ) (v : Vis n 1) (b : Bool) :
    twistRho n v = some b ↔ b = false ∧ ∃ i : Fin n, ∃ c : Bool, v = mkBad n i c := by
  cases v with
  | inl i =>
    simp [twistRho, mkBad]
  | inr p =>
    rcases p with ⟨i, t⟩
    simp only [twistRho]
    constructor
    · intro h
      by_cases ht : isTwist n i t = true
      · simp only [ht, ↓reduceIte] at h
        have hb : b = false := (Option.some.inj h).symm
        refine ⟨hb, i, t 0, ?_⟩
        simp only [mkBad, Sum.inr.injEq, Prod.mk.injEq, true_and]
        funext j
        match j with
        | ⟨0, _⟩ => rfl
        | ⟨1, _⟩ =>
          change t 1 = if i.val + 1 < n then !(t 0) else t 0
          simp only [isTwist] at ht
          split_ifs at ht ⊢ with hi
          · cases h0 : t 0 <;> cases h1 : t 1 <;> simp [h0, h1] at ht ⊢
          · cases h0 : t 0 <;> cases h1 : t 1 <;> simp [h0, h1] at ht ⊢
      · simp [ht] at h
    · rintro ⟨rfl, i', c, h⟩
      simp only [mkBad, Sum.inr.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      have ht : isTwist n i (fun j : Fin 2 => if j.val = 0 then c else if i.val + 1 < n then !c else c) = true := by
        simp only [isTwist, Fin.val_zero, ↓reduceIte, Fin.val_one, one_ne_zero]
        split_ifs <;> cases c <;> simp
      simp only [ht, ↓reduceIte]

lemma twist_unsat {n : ℕ} (hn : 0 < n) : ¬ ∃ a : Vis n 1 → Bool, Completion n 1 hn (twistRho n) a := by
  rintro ⟨a, ha, hρ⟩
  have hconst : ∀ k : ℕ, (hk : k < n) → a (Sum.inl ⟨k, hk⟩) = a (Sum.inl ⟨0, hn⟩) := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      have hkl : k < n := by omega
      let i : Fin n := ⟨k, hkl⟩
      have hai := ha i
      let t : Fin 2 → Bool := fun j => a (Sum.inl ⟨(k + j.val) % n, Nat.mod_lt _ hn⟩)
      have hnot : isTwist n i t = false := by
        by_contra hne
        have ht : isTwist n i t = true := by cases h : isTwist n i t <;> simp_all
        have hf := hρ (Sum.inr (i, t)) false (by simp [twistRho, ht])
        rw [hai] at hf
        simp at hf
      have hi1 : i.val + 1 < n := hk
      simp only [isTwist, hi1, ↓reduceIte, bne_eq_false_iff_eq] at hnot
      have ht0 : t 0 = a (Sum.inl ⟨k, hkl⟩) := by
        simp only [t, Fin.val_zero, add_zero, Nat.mod_eq_of_lt hkl]
      have ht1 : t 1 = a (Sum.inl ⟨k + 1, hk⟩) := by
        simp only [t, Fin.val_one, Nat.mod_eq_of_lt hk]
      rw [ht0, ht1] at hnot
      rw [← hnot, ih hkl]
  let ilast : Fin n := ⟨n - 1, by omega⟩
  have halast := ha ilast
  let t : Fin 2 → Bool := fun j => a (Sum.inl ⟨(ilast.val + j.val) % n, Nat.mod_lt _ hn⟩)
  have ht0 : t 0 = a (Sum.inl ⟨0, hn⟩) := by
    have hidx : (ilast.val + (0 : Fin 2).val) % n = n - 1 := by
      simp only [ilast, Fin.val_zero, add_zero]; exact Nat.mod_eq_of_lt (by omega)
    have hfin : (⟨(ilast.val + (0 : Fin 2).val) % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨n - 1, by omega⟩ := Fin.ext hidx
    change a (Sum.inl ⟨(ilast.val + (0 : Fin 2).val) % n, Nat.mod_lt _ hn⟩) = _
    rw [hfin]
    exact hconst (n - 1) (by omega)
  have ht1 : t 1 = a (Sum.inl ⟨0, hn⟩) := by
    have hidx : (ilast.val + (1 : Fin 2).val) % n = 0 := by
      have : ilast.val + 1 = n := by simp [ilast]; omega
      simp only [Fin.val_one, this, Nat.mod_self]
    have hfin : (⟨(ilast.val + (1 : Fin 2).val) % n, Nat.mod_lt _ hn⟩ : Fin n) = ⟨0, hn⟩ := Fin.ext hidx
    change a (Sum.inl ⟨(ilast.val + (1 : Fin 2).val) % n, Nat.mod_lt _ hn⟩) = _
    rw [hfin]
  have htw : isTwist n ilast t = true := by
    have hnotlt : ¬ (ilast.val + 1 < n) := by simp [ilast]; omega
    simp [isTwist, hnotlt, ht0, ht1]
  have hf := hρ (Sum.inr (ilast, t)) false (by simp [twistRho, htw])
  rw [halast] at hf
  simp at hf

lemma twist_erase_sat {n : ℕ} (hn : 0 < n) (i0 : Fin n) (b0 : Bool) :
    ∃ a : Vis n 1 → Bool, Completion n 1 hn
      (fun v => if v = mkBad n i0 b0 then none else twistRho n v) a := by
  classical
  let ρ' : Vis n 1 → Option Bool := fun v => if v = mkBad n i0 b0 then none else twistRho n v
  let word : Fin n → Bool := fun i =>
    if i0.val + 1 < n then (if i.val ≤ i0.val then b0 else !b0) else b0
  let a : Vis n 1 → Bool := fun v =>
    match v with
    | Sum.inl i => word i
    | Sum.inr p => match ρ' (Sum.inr p) with
      | some b => b
      | none => true
  refine ⟨a, ?_, ?_⟩
  · intro i
    let t : Fin 2 → Bool := fun j => word ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩
    have hgoal : a (Sum.inr (i, t)) = true := by
      suffices hnone : ρ' (Sum.inr (i, t)) = none by simp [a, hnone]
      by_cases hbad : Sum.inr (i, t) = mkBad n i0 b0
      · simp [ρ', hbad]
      · simp only [ρ', hbad, ↓reduceIte, twistRho]
        suffices htw : isTwist n i t = false by simp [htw]
        by_cases hi0 : i0.val + 1 < n
        · by_cases hi : i.val + 1 < n
          · have ht0 : t 0 = if i.val ≤ i0.val then b0 else !b0 := by
              change word ⟨(i.val + 0) % n, _⟩ = _
              simp only [word, hi0, ↓reduceIte, add_zero, Nat.mod_eq_of_lt i.isLt]
            have ht1 : t 1 = if i.val + 1 ≤ i0.val then b0 else !b0 := by
              change word ⟨(i.val + 1) % n, _⟩ = _
              simp only [word, hi0, ↓reduceIte, Nat.mod_eq_of_lt hi]
            by_cases hlt : i.val < i0.val
            · have h1 : i.val ≤ i0.val := by omega
              have h2 : i.val + 1 ≤ i0.val := by omega
              simp [isTwist, hi, ht0, ht1, h1, h2]
            · by_cases heq : i.val = i0.val
              · exfalso
                apply hbad
                have hiEq : i = i0 := Fin.ext heq
                subst hiEq
                simp only [mkBad, Sum.inr.injEq, Prod.mk.injEq, true_and]
                funext j
                match j with
                | ⟨0, _⟩ => simp [ht0]
                | ⟨1, _⟩ =>
                  have h1 : ¬ (i.val + 1 ≤ i.val) := by omega
                  change t 1 = _
                  simp [ht1, h1, hi0]
              · have h1 : ¬ (i.val ≤ i0.val) := by omega
                have h2 : ¬ (i.val + 1 ≤ i0.val) := by omega
                simp [isTwist, hi, ht0, ht1, h1, h2]
          · have hival : i.val + 1 = n := by omega
            have ht0 : t 0 = !b0 := by
              have h1 : ¬ (i.val ≤ i0.val) := by omega
              change word ⟨(i.val + 0) % n, _⟩ = _
              simp only [word, hi0, ↓reduceIte, add_zero, Nat.mod_eq_of_lt i.isLt, h1]
            have ht1 : t 1 = b0 := by
              have hmod : (i.val + 1) % n = 0 := by rw [hival, Nat.mod_self]
              have h0 : 0 ≤ i0.val := Nat.zero_le _
              change word ⟨(i.val + 1) % n, _⟩ = _
              simp only [word, hi0, ↓reduceIte, hmod, h0]
            simp [isTwist, hi, ht0, ht1]
        · have ht0 : t 0 = b0 := by simp [t, word, hi0]
          have ht1 : t 1 = b0 := by simp [t, word, hi0]
          by_cases hi : i.val + 1 < n
          · simp [isTwist, hi, ht0, ht1]
          · exfalso
            apply hbad
            have hiEq : i = i0 := Fin.ext (by omega)
            subst hiEq
            simp only [mkBad, Sum.inr.injEq, Prod.mk.injEq, true_and]
            funext j
            match j with
            | ⟨0, _⟩ => simp [ht0]
            | ⟨1, _⟩ =>
              change t 1 = _
              simp [ht1, hi0]
    exact hgoal
  · intro v b hrv
    cases v with
    | inl i =>
      by_cases hbad : Sum.inl i = mkBad n i0 b0
      · simp [hbad] at hrv
      · simp [hbad, twistRho] at hrv
    | inr p =>
      have hrv' : ρ' (Sum.inr p) = some b := hrv
      change (match ρ' (Sum.inr p) with | some b => b | none => true) = b
      rw [hrv']

lemma lower_bound_w1 {n d m : ℕ} (hn : 0 < n)
    (F : Finset (Cl (Sum (Vis n 1) (Fin m))))
    (hcard : ∀ D ∈ F, D.card ≤ 3)
    (hforce : ∀ ρ : Vis n 1 → Option Bool,
      (∃ a : Vis n 1 → Bool, Completion n 1 hn ρ a) →
      ∀ v : Vis n 1, ∀ b : Bool,
        (∀ a : Vis n 1 → Bool, Completion n 1 hn ρ a → a v = b) ↔
        (Sum.inl v, b) ∈ (upStep F)^[d] (seedOf ρ)) :
    Nat.clog 2 n + 1 ≤ d := by
  classical
  by_contra hlt
  push Not at hlt
  let i0 : Fin n := ⟨0, hn⟩
  let v0 : Vis n 1 := mkBad n i0 false
  let ρ1 : Vis n 1 → Option Bool := fun v => if v = v0 then none else twistRho n v
  have hcomp1 : ∃ a : Vis n 1 → Bool, Completion n 1 hn ρ1 a := twist_erase_sat hn i0 false
  have hforced1 : ∀ a : Vis n 1 → Bool, Completion n 1 hn ρ1 a → a v0 = true := by
    intro a ⟨ha, hρ1⟩
    by_contra hne
    have hf : a v0 = false := by cases h : a v0 <;> simp_all
    apply twist_unsat hn
    refine ⟨a, ha, ?_⟩
    intro v b hrv
    by_cases hv : v = v0
    · subst hv
      have hb : b = false := ((twistRho_eq_some_iff n v0 b).1 hrv).1
      rw [hb, hf]
    · exact hρ1 v b (by simp [ρ1, hv, hrv])
  have hmem1 : (Sum.inl v0, true) ∈ (upStep F)^[d] (seedOf ρ1) :=
    (hforce ρ1 hcomp1 v0 true).1 hforced1
  cases d with
  | zero =>
    simp only [Function.iterate_zero, id_eq, seedOf] at hmem1
    rcases hmem1 with ⟨v, hv, hrv⟩
    have hveq : v = v0 := Sum.inl.inj hv.symm
    subst hveq
    simp [ρ1] at hrv
  | succ d' =>
    have hdlt : d' < Nat.clog 2 n := by omega
    have hpow : 2 ^ d' < n := (Nat.lt_clog_iff_pow_lt (by omega)).1 hdlt
    have hpow2 : 2 ^ (d' + 1) < 2 * n - 1 := by
      have : 2 ^ (d' + 1) = 2 * 2 ^ d' := by ring
      omega
    obtain ⟨T, hTS, hTcard, hmemT⟩ := upStep_support hcard (seedOf ρ1) (d' + 1) (Sum.inl v0, true) hmem1
    let S0 : Finset (Vis n 1) := Finset.univ.image (fun p : Fin n × Bool => mkBad n p.1 p.2)
    have hS0card : S0.card = 2 * n := by
      rw [Finset.card_image_of_injective _ (mkBad_injective n)]
      simp [Fintype.card_prod]
      ring
    have hv0S0 : v0 ∈ S0 := Finset.mem_image.2 ⟨(i0, false), Finset.mem_univ _, rfl⟩
    let E0 : Finset (Vis n 1) := S0.erase v0
    have hE0card : E0.card = 2 * n - 1 := by
      have h1 : E0.card + 1 = S0.card := Finset.card_erase_add_one hv0S0
      omega
    let U : Finset (Vis n 1) := E0.filter (fun v => (Sum.inl v, false) ∈ T)
    have hUcard : U.card ≤ T.card := by
      let f : Vis n 1 → Lit (Sum (Vis n 1) (Fin m)) := fun v => (Sum.inl v, false)
      have hfinj : Function.Injective f := by
        intro x y h
        simp only [f, Prod.mk.injEq, Sum.inl.injEq] at h
        exact h.1
      have hsub : U.image f ⊆ T := by
        intro l hl
        rcases Finset.mem_image.1 hl with ⟨v, hv, rfl⟩
        exact (Finset.mem_filter.1 hv).2
      rw [← Finset.card_image_of_injective U hfinj]
      exact Finset.card_le_card hsub
    have hUlt : U.card < E0.card := by omega
    have hne : (E0 \ U).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hemp
      have hsub : E0 ⊆ U := Finset.sdiff_eq_empty_iff_subset.1 hemp
      have := Finset.card_le_card hsub
      omega
    obtain ⟨v1, hv1⟩ := hne
    have hv1E0 : v1 ∈ E0 := (Finset.mem_sdiff.1 hv1).1
    have hv1notU : v1 ∉ U := (Finset.mem_sdiff.1 hv1).2
    have hv1ne : v1 ≠ v0 := Finset.ne_of_mem_erase hv1E0
    have hv1S0 : v1 ∈ S0 := Finset.mem_of_mem_erase hv1E0
    have hv1notT : (Sum.inl v1, false) ∉ T := by
      intro hmem
      exact hv1notU (Finset.mem_filter.2 ⟨hv1E0, hmem⟩)
    rcases Finset.mem_image.1 hv1S0 with ⟨⟨i1, b1⟩, _, hv1eq⟩
    dsimp only at hv1eq
    let ρ2 : Vis n 1 → Option Bool := fun v =>
      if v = v0 ∨ v = v1 then none else twistRho n v
    have hTsub : (↑T : Set (Lit (Sum (Vis n 1) (Fin m)))) ⊆ seedOf ρ2 := by
      intro l hlT
      have hl1 := hTS l (Finset.mem_coe.1 hlT)
      rcases hl1 with ⟨v, hv, hrv⟩
      have hnv0 : v ≠ v0 := by
        intro hEq; subst hEq; simp [ρ1] at hrv
      simp only [ρ1, hnv0, ↓reduceIte] at hrv
      have hb : l.2 = false := ((twistRho_eq_some_iff n v l.2).1 hrv).1
      have hnv1 : v ≠ v1 := by
        intro hEq
        apply hv1notT
        have hleq : l = (Sum.inl v1, false) := Prod.ext (by rw [hv, hEq]) hb
        rw [← hleq]
        exact Finset.mem_coe.1 hlT
      exact ⟨v, hv, by simp [ρ2, hnv0, hnv1, hrv]⟩
    have hmem2 : (Sum.inl v0, true) ∈ (upStep F)^[d' + 1] (seedOf ρ2) :=
      upStep_iter_mono Finset.Subset.rfl hTsub (d' + 1) hmemT
    obtain ⟨a, ha, hρa⟩ := twist_erase_sat hn i1 b1
    have hcomp2 : Completion n 1 hn ρ2 a := by
      refine ⟨ha, ?_⟩
      intro v b hrv2
      by_cases h01 : v = v0 ∨ v = v1
      · simp [ρ2, h01] at hrv2
      · push Not at h01
        simp only [ρ2, h01.1, h01.2, or_self, ↓reduceIte] at hrv2
        have hnv1' : v ≠ mkBad n i1 b1 := by rw [hv1eq]; exact h01.2
        exact hρa v b (by simp [hnv1', hrv2])
    have haTrue : a v0 = true := (hforce ρ2 ⟨a, hcomp2⟩ v0 true).2 hmem2 a hcomp2
    have haFalse : a v0 = false := by
      have hnv1' : v0 ≠ mkBad n i1 b1 := by rw [hv1eq]; exact hv1ne.symm
      have htw0 : twistRho n v0 = some false :=
        (twistRho_eq_some_iff n v0 false).2 ⟨rfl, i0, false, rfl⟩
      exact hρa v0 false (by simp [hnv1', htw0])
    rw [haTrue] at haFalse
    simp at haFalse

lemma sum_toFinset_card_le {W : Type} [DecidableEq (Cl W)] (L : List (Cl W)) :
    (∑ D ∈ L.toFinset, D.card) ≤ (L.map Finset.card).sum := by
  induction L with
  | nil => simp
  | cons C rest ih =>
    simp only [List.toFinset_cons, List.map_cons, List.sum_cons]
    by_cases hC : C ∈ rest.toFinset
    · rw [Finset.insert_eq_of_mem hC]
      omega
    · rw [Finset.sum_insert hC]
      omega

lemma sum_map_card_le {W : Type} (L : List (Cl W)) (k : ℕ) (h : ∀ C ∈ L, C.card ≤ k) :
    (L.map Finset.card).sum ≤ k * L.length := by
  induction L with
  | nil => simp
  | cons C rest ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    have hC : C.card ≤ k := h C (List.mem_cons_self ..)
    have hrest := ih (fun D hD => h D (List.mem_cons_of_mem C hD))
    have : k * (rest.length + 1) = k + k * rest.length := by ring
    omega

lemma upper_bound_w0 (n : ℕ) (hn : 0 < n) :
    let height := Nat.clog 2 n
    ∃ (m : ℕ) (F : Finset (Cl (Sum (Vis n 0) (Fin m)))),
      (∀ D ∈ F, D.card ≤ 3) ∧
      (∀ total : Vis n 0 → Bool, Accepts n 0 hn total ↔ ∃ aux : Fin m → Bool,
        PEqualNP.ProofComplexity.Satisfies (Sum.elim total aux) (↑F : Set (Cl (Sum (Vis n 0) (Fin m))))) ∧
      (∀ ρ : Vis n 0 → Option Bool,
        ((¬ ∃ a : Vis n 0 → Bool, Completion n 0 hn ρ a) ↔
          ∃ D ∈ F, ∀ l ∈ D, negL l ∈ (upStep F)^[1] (seedOf ρ)) ∧
        ((∃ a : Vis n 0 → Bool, Completion n 0 hn ρ a) → ∀ v : Vis n 0, ∀ b : Bool,
          (∀ a : Vis n 0 → Bool, Completion n 0 hn ρ a → a v = b) ↔
          (Sum.inl v, b) ∈ (upStep F)^[1] (seedOf ρ))) ∧
      m + (∑ D ∈ F, D.card) ≤ 256 * (n + 1) * (height + 1) * 16 ^ 0 := by
  classical
  let c0 : Fin n → Cl (Sum (Vis n 0) (Fin 0)) := fun i =>
    {(Sum.inl (Sum.inl i), true), (Sum.inl (Sum.inr (i, fun _ => false)), true)}
  let c1 : Fin n → Cl (Sum (Vis n 0) (Fin 0)) := fun i =>
    {(Sum.inl (Sum.inl i), false), (Sum.inl (Sum.inr (i, fun _ => true)), true)}
  let c2 : Fin n → Cl (Sum (Vis n 0) (Fin 0)) := fun i =>
    {(Sum.inl (Sum.inr (i, fun _ => false)), true), (Sum.inl (Sum.inr (i, fun _ => true)), true)}
  let L : List (Cl (Sum (Vis n 0) (Fin 0))) :=
    (List.finRange n).map c0 ++ (List.finRange n).map c1 ++ (List.finRange n).map c2
  let F : Finset (Cl (Sum (Vis n 0) (Fin 0))) := L.toFinset
  have hc0F : ∀ i, c0 i ∈ F := fun i =>
    List.mem_toFinset.2 (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩)))
  have hc1F : ∀ i, c1 i ∈ F := fun i =>
    List.mem_toFinset.2 (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩)))
  have hc2F : ∀ i, c2 i ∈ F := fun i =>
    List.mem_toFinset.2 (List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩))
  have hcard2 : ∀ D ∈ L, D.card ≤ 2 := by
    intro D hD
    simp only [L, List.mem_append, List.mem_map] at hD
    rcases hD with (⟨i, _, rfl⟩ | ⟨i, _, rfl⟩) | ⟨i, _, rfl⟩
    · exact Finset.card_le_two
    · exact Finset.card_le_two
    · exact Finset.card_le_two
  have hcard3 : ∀ D ∈ F, D.card ≤ 3 := fun D hD => (hcard2 D (List.mem_toFinset.1 hD)).trans (by omega)
  have hfn0 : ∀ (a : Vis n 0 → Bool) (i : Fin n),
      (fun j : Fin 1 => a (Sum.inl ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩)) =
      (fun _ : Fin 1 => a (Sum.inl i)) := by
    intro a i
    funext j
    have hj0 : j.val = 0 := by omega
    have hidx : (⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩ : Fin n) = i := by
      apply Fin.ext; simp [Nat.mod_eq_of_lt i.isLt]
    rw [hidx]
  have hsat : ∀ total : Vis n 0 → Bool, Accepts n 0 hn total ↔ ∃ aux : Fin 0 → Bool,
      PEqualNP.ProofComplexity.Satisfies (Sum.elim total aux) (↑F : Set _) := by
    intro total
    constructor
    · intro hacc
      refine ⟨Fin.elim0, ?_⟩
      intro D hD
      have hDL : D ∈ L := List.mem_toFinset.1 hD
      simp only [L, List.mem_append, List.mem_map] at hDL
      rcases hDL with (⟨i, _, rfl⟩ | ⟨i, _, rfl⟩) | ⟨i, _, rfl⟩
      · cases hxi : total (Sum.inl i)
        · have hi := hacc i
          rw [hfn0 total i, hxi] at hi
          exact ⟨(Sum.inl (Sum.inr (i, fun _ => false)), true), by simp [c0], hi⟩
        · exact ⟨(Sum.inl (Sum.inl i), true), by simp [c0], hxi⟩
      · cases hxi : total (Sum.inl i)
        · exact ⟨(Sum.inl (Sum.inl i), false), by simp [c1], hxi⟩
        · have hi := hacc i
          rw [hfn0 total i, hxi] at hi
          exact ⟨(Sum.inl (Sum.inr (i, fun _ => true)), true), by simp [c1], hi⟩
      · cases hxi : total (Sum.inl i)
        · have hi := hacc i
          rw [hfn0 total i, hxi] at hi
          exact ⟨(Sum.inl (Sum.inr (i, fun _ => false)), true), by simp [c2], hi⟩
        · have hi := hacc i
          rw [hfn0 total i, hxi] at hi
          exact ⟨(Sum.inl (Sum.inr (i, fun _ => true)), true), by simp [c2], hi⟩
    · rintro ⟨aux, haux⟩ i
      rw [hfn0 total i]
      cases hxi : total (Sum.inl i)
      · obtain ⟨l, hl, hsatl⟩ := haux (c0 i) (hc0F i)
        simp only [c0, Finset.mem_insert, Finset.mem_singleton] at hl
        rcases hl with rfl | rfl
        · simp [hxi] at hsatl
        · exact hsatl
      · obtain ⟨l, hl, hsatl⟩ := haux (c1 i) (hc1F i)
        simp only [c1, Finset.mem_insert, Finset.mem_singleton] at hl
        rcases hl with rfl | rfl
        · simp [hxi] at hsatl
        · exact hsatl
  refine ⟨0, F, hcard3, hsat, ?_, ?_⟩
  · intro ρ
    let okBit : Fin n → Bool → Prop := fun i b =>
      ρ (Sum.inl i) ≠ some (!b) ∧ ρ (Sum.inr (i, fun _ => b)) ≠ some false
    have hsat_iff : (∃ a : Vis n 0 → Bool, Completion n 0 hn ρ a) ↔ ∀ i : Fin n, ∃ b : Bool, okBit i b := by
      constructor
      · rintro ⟨a, ha, hρ⟩ i
        refine ⟨a (Sum.inl i), ?_, ?_⟩
        · intro h
          have := hρ (Sum.inl i) (!(a (Sum.inl i))) h
          cases hxi : a (Sum.inl i) <;> simp [hxi] at this
        · intro h
          have h1 := hρ (Sum.inr (i, fun _ => a (Sum.inl i))) false h
          have h2 := ha i
          rw [hfn0 a i] at h2
          rw [h1] at h2
          simp at h2
      · intro hok
        choose f hf using hok
        let a : Vis n 0 → Bool := fun v =>
          match v with
          | Sum.inl i => f i
          | Sum.inr p => match ρ (Sum.inr p) with
            | some b => b
            | none => true
        refine ⟨a, ?_, ?_⟩
        · intro i
          rw [hfn0 a i]
          change (match ρ (Sum.inr (i, fun _ => f i)) with | some b => b | none => true) = true
          cases hrv : ρ (Sum.inr (i, fun _ => f i)) with
          | none => rfl
          | some b =>
            cases b
            · exact absurd hrv (hf i).2
            · rfl
        · intro v b hrv
          cases v with
          | inl i =>
            change f i = b
            by_contra hne
            have hnb : b = !(f i) := bool_eq_not_of_ne hne
            rw [hnb] at hrv
            exact (hf i).1 hrv
          | inr p =>
            change (match ρ (Sum.inr p) with | some b => b | none => true) = b
            rw [hrv]
    have hseed : ∀ (v : Vis n 0) (b : Bool), ρ v = some b →
        (Sum.inl v, b) ∈ (upStep F)^[1] (seedOf ρ) := fun v b hrv =>
      subset_upStep F (seedOf ρ) ⟨v, rfl, hrv⟩
    have hstep2 : ∀ {l1 l2 : Lit (Sum (Vis n 0) (Fin 0))},
        ({l1, l2} : Cl _) ∈ F → negL l1 ∈ seedOf ρ → l2 ∈ (upStep F)^[1] (seedOf ρ) := by
      intro l1 l2 hC hl1
      simp only [Function.iterate_one]
      refine Or.inr ⟨{l1, l2}, hC, by simp, ?_⟩
      intro o ho hne
      simp only [Finset.mem_insert, Finset.mem_singleton] at ho
      rcases ho with rfl | rfl
      · exact hl1
      · exact absurd rfl hne
    constructor
    · constructor
      · intro hno
        have hnotall : ¬ ∀ i : Fin n, ∃ b : Bool, okBit i b := fun h => hno (hsat_iff.2 h)
        push Not at hnotall
        obtain ⟨i, hi⟩ := hnotall
        have h0 : ρ (Sum.inl i) = some true ∨ ρ (Sum.inr (i, fun _ => false)) = some false := by
          have := hi false
          simp only [okBit, Bool.not_false] at this
          tauto
        have h1 : ρ (Sum.inl i) = some false ∨ ρ (Sum.inr (i, fun _ => true)) = some false := by
          have := hi true
          simp only [okBit, Bool.not_true] at this
          tauto
        rcases h0 with hxT | hp0 <;> rcases h1 with hxF | hp1
        · rw [hxT] at hxF; simp at hxF
        · refine ⟨c1 i, hc1F i, ?_⟩
          intro l hl
          simp only [c1, Finset.mem_insert, Finset.mem_singleton] at hl
          rcases hl with rfl | rfl
          · exact hseed (Sum.inl i) true hxT
          · exact hseed (Sum.inr (i, fun _ => true)) false hp1
        · refine ⟨c0 i, hc0F i, ?_⟩
          intro l hl
          simp only [c0, Finset.mem_insert, Finset.mem_singleton] at hl
          rcases hl with rfl | rfl
          · exact hseed (Sum.inl i) false hxF
          · exact hseed (Sum.inr (i, fun _ => false)) false hp0
        · refine ⟨c2 i, hc2F i, ?_⟩
          intro l hl
          simp only [c2, Finset.mem_insert, Finset.mem_singleton] at hl
          rcases hl with rfl | rfl
          · exact hseed (Sum.inr (i, fun _ => false)) false hp0
          · exact hseed (Sum.inr (i, fun _ => true)) false hp1
      · intro hconf hcomp
        exact enc_conflict_sound (fun t ht => (hsat t).1 ht) hcomp hconf
    · intro hcomp v b
      constructor
      · intro hforced
        cases hrv : ρ v with
        | some b' =>
          obtain ⟨a, ha⟩ := hcomp
          have hb1 : a v = b' := ha.2 v b' hrv
          have hb2 : a v = b := hforced a ha
          have hbe : b' = b := hb1.symm.trans hb2
          subst hbe
          exact hseed v b' hrv
        | none =>
          have hokall := hsat_iff.1 hcomp
          cases v with
          | inl i =>
            have hnotb : ¬ okBit i (!b) := by
              intro hoknb
              let ρ' : Vis n 0 → Option Bool := fun u => if u = Sum.inl i then some (!b) else ρ u
              have hok' : ∀ j : Fin n, ∃ c : Bool,
                  ρ' (Sum.inl j) ≠ some (!c) ∧ ρ' (Sum.inr (j, fun _ => c)) ≠ some false := by
                intro j
                by_cases hj : j = i
                · subst hj
                  refine ⟨!b, ?_, ?_⟩
                  · simp [ρ']
                  · simpa [ρ'] using hoknb.2
                · obtain ⟨c, hc⟩ := hokall j
                  refine ⟨c, ?_, ?_⟩
                  · simpa [ρ', hj] using hc.1
                  · simpa [ρ'] using hc.2
              choose f hf using hok'
              let a : Vis n 0 → Bool := fun u =>
                match u with
                | Sum.inl j => f j
                | Sum.inr p => match ρ' (Sum.inr p) with
                  | some c => c
                  | none => true
              have hcompa : Completion n 0 hn ρ a := by
                refine ⟨?_, ?_⟩
                · intro j
                  rw [hfn0 a j]
                  change (match ρ' (Sum.inr (j, fun _ => f j)) with | some c => c | none => true) = true
                  cases hu : ρ' (Sum.inr (j, fun _ => f j)) with
                  | none => rfl
                  | some c =>
                    cases c
                    · exact absurd hu (hf j).2
                    · rfl
                · intro u c hru
                  cases u with
                  | inl j =>
                    change f j = c
                    by_cases hj : j = i
                    · subst hj; rw [hrv] at hru; simp at hru
                    · by_contra hne
                      have hnc : c = !(f j) := bool_eq_not_of_ne hne
                      rw [hnc] at hru
                      exact (hf j).1 (by simp [ρ', hj, hru])
                  | inr p =>
                    change (match ρ' (Sum.inr p) with | some c => c | none => true) = c
                    simp [ρ', hru]
              have hfi : f i = !b := by
                by_contra hne
                have hnb : (!b) = !(f i) := bool_eq_not_of_ne hne
                exact (hf i).1 (by simp [ρ', hnb])
              have hab : a (Sum.inl i) = b := hforced a hcompa
              change f i = b at hab
              rw [hfi] at hab
              cases b <;> simp at hab
            have hp : ρ (Sum.inr (i, fun _ => !b)) = some false := by
              simp only [okBit, hrv] at hnotb
              cases h : ρ (Sum.inr (i, fun _ => !b)) with
              | none => exact absurd ⟨by simp, by simp [h]⟩ hnotb
              | some c =>
                cases c
                · rfl
                · exact absurd ⟨by simp, by simp [h]⟩ hnotb
            cases b
            · have hC : ({(Sum.inl (Sum.inr (i, fun _ => true)), true), (Sum.inl (Sum.inl i), false)} : Cl _) ∈ F := by
                simpa [c1, Finset.pair_comm] using hc1F i
              exact hstep2 hC ⟨Sum.inr (i, fun _ => true), rfl, by simpa [negL, PEqualNP.Search.negLit] using hp⟩
            · have hC : ({(Sum.inl (Sum.inr (i, fun _ => false)), true), (Sum.inl (Sum.inl i), true)} : Cl _) ∈ F := by
                simpa [c0, Finset.pair_comm] using hc0F i
              exact hstep2 hC ⟨Sum.inr (i, fun _ => false), rfl, by simpa [negL, PEqualNP.Search.negLit] using hp⟩
          | inr p =>
            rcases p with ⟨i, t⟩
            have ht : t = fun _ => t 0 := by
              funext j
              have hj0 : j = 0 := Fin.ext (by omega)
              rw [hj0]
            rw [ht] at hrv hforced ⊢
            have hbT : b = true := by
              obtain ⟨a, ha, hρa⟩ := hcomp
              let a' : Vis n 0 → Bool := fun u =>
                if u = Sum.inr (i, fun _ => t 0) then true else a u
              have hcomp' : Completion n 0 hn ρ a' := by
                refine ⟨?_, ?_⟩
                · intro j
                  have h1 : ∀ u : Fin n, a' (Sum.inl u) = a (Sum.inl u) := fun _ => by simp [a']
                  rw [hfn0 a' j, h1 j]
                  by_cases heq : (Sum.inr (j, fun _ => a (Sum.inl j)) : Vis n 0) = Sum.inr (i, fun _ => t 0)
                  · simp [a', heq]
                  · have hj := ha j
                    rw [hfn0 a j] at hj
                    simp [a', heq, hj]
                · intro u c hru
                  by_cases heq : u = Sum.inr (i, fun _ => t 0)
                  · subst heq; rw [hrv] at hru; simp at hru
                  · simp [a', heq, hρa u c hru]
              have := hforced a' hcomp'
              simpa [a'] using this.symm
            subst hbT
            have hnotother : ¬ okBit i (!(t 0)) := by
              intro hokother
              obtain ⟨a, ha, hρa⟩ := hcomp
              let a' : Vis n 0 → Bool := fun u =>
                if u = Sum.inl i then !(t 0)
                else if u = Sum.inr (i, fun _ => t 0) then false
                else if u = Sum.inr (i, fun _ => !(t 0)) then true
                else a u
              have hcomp' : Completion n 0 hn ρ a' := by
                refine ⟨?_, ?_⟩
                · intro j
                  rw [hfn0 a' j]
                  by_cases hj : j = i
                  · subst hj
                    have hne : (fun _ : Fin 1 => !(t 0)) ≠ (fun _ : Fin 1 => t 0) := by
                      intro h; have := congrFun h 0; cases t 0 <;> simp at this
                    simp [a', hne]
                  · have hne1 : (Sum.inr (j, fun _ => a (Sum.inl j)) : Vis n 0) ≠ Sum.inr (i, fun _ => t 0) := by simp [hj]
                    have hne2 : (Sum.inr (j, fun _ => a (Sum.inl j)) : Vis n 0) ≠ Sum.inr (i, fun _ => !(t 0)) := by simp [hj]
                    have hj' := ha j
                    rw [hfn0 a j] at hj'
                    simp [a', hj, hne1, hne2, hj']
                · intro u c hru
                  by_cases h1 : u = Sum.inl i
                  · subst h1
                    have hne : t 0 ≠ c := by
                      intro hEq; subst hEq
                      exact hokother.1 (by simpa using hru)
                    have hce : (!(t 0)) = c := (bool_eq_not_of_ne hne).symm
                    simp [a', hce]
                  · by_cases h2 : u = Sum.inr (i, fun _ => t 0)
                    · subst h2; rw [hrv] at hru; simp at hru
                    · by_cases h3 : u = Sum.inr (i, fun _ => !(t 0))
                      · subst h3
                        cases c
                        · exact absurd hru hokother.2
                        · simp [a', h1, h2]
                      · simp [a', h1, h2, h3, hρa u c hru]
              have := hforced a' hcomp'
              simp [a'] at this
            have hdisj : ρ (Sum.inl i) = some (t 0) ∨ ρ (Sum.inr (i, fun _ => !(t 0))) = some false := by
              simp only [okBit, Bool.not_not] at hnotother
              tauto
            cases ht0 : t 0
            · rw [ht0] at hdisj
              rcases hdisj with hx | hp
              · exact hstep2 (hc0F i) ⟨Sum.inl i, rfl, by simpa [negL, PEqualNP.Search.negLit] using hx⟩
              · have hC : ({(Sum.inl (Sum.inr (i, fun _ => true)), true), (Sum.inl (Sum.inr (i, fun _ => false)), true)} : Cl _) ∈ F := by
                  simpa [c2, Finset.pair_comm] using hc2F i
                exact hstep2 hC ⟨Sum.inr (i, fun _ => true), rfl, by simpa [negL, PEqualNP.Search.negLit] using hp⟩
            · rw [ht0] at hdisj
              rcases hdisj with hx | hp
              · exact hstep2 (hc1F i) ⟨Sum.inl i, rfl, by simpa [negL, PEqualNP.Search.negLit] using hx⟩
              · exact hstep2 (hc2F i) ⟨Sum.inr (i, fun _ => false), rfl, by simpa [negL, PEqualNP.Search.negLit] using hp⟩
      · exact enc_force_sound (fun t ht => (hsat t).1 ht)
  · have hsum1 : (∑ D ∈ F, D.card) ≤ (L.map Finset.card).sum := sum_toFinset_card_le L
    have hsum2 : (L.map Finset.card).sum ≤ 2 * L.length := sum_map_card_le L 2 hcard2
    have hLlen : L.length = 3 * n := by simp [L]; ring
    have h1 : 1 ≤ Nat.clog 2 n + 1 := by omega
    nlinarith

abbrev State (w : ℕ) := Fin w → Bool
abbrev FailR (W : Type) := Option (List (Lit W))
abbrev MatRep (w : ℕ) (W : Type) := State w → State w → FailR W
abbrev St (W : Type) := ℕ × List (Cl W)
abbrev TestSpec (n w : ℕ) := Fin n × Sum Bool (Fin (w + 1) → Bool)

def stCost {W : Type} (st : St W) : ℕ := st.1 + 3 * st.2.length

def allTuples : (k : ℕ) → List (Fin k → Bool)
  | 0 => [Fin.elim0]
  | k + 1 => (allTuples k).map (Fin.cons false) ++ (allTuples k).map (Fin.cons true)

lemma allTuples_length : ∀ k : ℕ, (allTuples k).length = 2 ^ k
  | 0 => rfl
  | k + 1 => by
    simp only [allTuples, List.length_append, List.length_map, allTuples_length k]
    ring

lemma mem_allTuples : ∀ (k : ℕ) (t : Fin k → Bool), t ∈ allTuples k
  | 0, t => by
    have ht : t = Fin.elim0 := funext (fun i => Fin.elim0 i)
    simp [allTuples, ht]
  | k + 1, t => by
    let tail : Fin k → Bool := fun i => t i.succ
    have ht : t = Fin.cons (t 0) tail := by
      funext j
      refine Fin.cases ?_ ?_ j
      · rfl
      · intro i; rfl
    rw [ht]
    cases t 0
    · exact List.mem_append_left _ (List.mem_map.2 ⟨tail, mem_allTuples k tail, rfl⟩)
    · exact List.mem_append_right _ (List.mem_map.2 ⟨tail, mem_allTuples k tail, rfl⟩)

def rowTests (n w : ℕ) (i : Fin n) : List (TestSpec n w) :=
  [(i, Sum.inl false), (i, Sum.inl true)] ++ (allTuples (w + 1)).map (fun t => (i, Sum.inr t))

lemma rowTests_length (n w : ℕ) (i : Fin n) : (rowTests n w i).length = 2 + 2 ^ (w + 1) := by
  simp [rowTests, allTuples_length]
  omega

lemma mem_rowTests (n w : ℕ) (i : Fin n) (T : TestSpec n w) :
    T ∈ rowTests n w i ↔ T.1 = i := by
  rcases T with ⟨i', spec⟩
  simp only [rowTests, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map]
  constructor
  · rintro ((h | h) | ⟨t, _, h⟩)
    · exact (Prod.mk.inj h).1
    · exact (Prod.mk.inj h).1
    · exact (Prod.mk.inj h).1.symm
  · intro hi
    subst hi
    cases spec with
    | inl b => cases b <;> simp
    | inr t => exact Or.inr ⟨t, mem_allTuples (w + 1) t, rfl⟩

def rangeTests (n w : ℕ) (lo len : ℕ) (hhi : lo + len ≤ n) : List (TestSpec n w) :=
  (List.finRange len).flatMap (fun k => rowTests n w ⟨lo + k.val, by omega⟩)

lemma list_flatMap_length_const {α β : Type} (L : List α) (f : α → List β) (c : ℕ)
    (hf : ∀ x ∈ L, (f x).length = c) : (L.flatMap f).length = L.length * c := by
  induction L with
  | nil => simp
  | cons a rest ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [hf a (List.mem_cons_self ..), ih (fun x hx => hf x (List.mem_cons_of_mem a hx))]
    ring

lemma rangeTests_length (n w lo len : ℕ) (hhi : lo + len ≤ n) :
    (rangeTests n w lo len hhi).length = len * (2 + 2 ^ (w + 1)) := by
  unfold rangeTests
  rw [list_flatMap_length_const _ _ (2 + 2 ^ (w + 1)) (fun k _ => rowTests_length n w _)]
  simp

lemma mem_rangeTests (n w lo len : ℕ) (hhi : lo + len ≤ n) (T : TestSpec n w) :
    T ∈ rangeTests n w lo len hhi ↔ lo ≤ T.1.val ∧ T.1.val < lo + len := by
  simp only [rangeTests, List.mem_flatMap, List.mem_finRange, true_and, mem_rowTests]
  constructor
  · rintro ⟨k, hk⟩
    rw [hk]
    exact ⟨Nat.le_add_right lo k.val, Nat.add_lt_add_left k.isLt lo⟩
  · rintro ⟨h1, h2⟩
    refine ⟨⟨T.1.val - lo, by omega⟩, ?_⟩
    apply Fin.ext
    simp; omega

def testLit {n w : ℕ} : TestSpec n w → Lit (Vis n w)
  | (i, Sum.inl b) => (Sum.inl i, b)
  | (i, Sum.inr t) => (Sum.inr (i, t), true)

def Fails {W : Type} (α : W → Bool) : FailR W → Prop
  | none => True
  | some R => ∃ r ∈ R, α r.1 = r.2

def KnownFail {W : Type} (K : Set (Lit W)) : FailR W → Prop
  | none => True
  | some R => ∃ r ∈ R, r ∈ K

def rLen {W : Type} : FailR W → ℕ
  | none => 0
  | some R => R.length

def ValidLit {V : Type} (m : ℕ) (l : Lit (Sum V ℕ)) : Prop :=
  ∀ k, l.1 = Sum.inr k → k < m

def ValidCl {V : Type} (m : ℕ) (C : Cl (Sum V ℕ)) : Prop :=
  ∀ l ∈ C, ValidLit m l

def ValidFailR {V : Type} (m : ℕ) : FailR (Sum V ℕ) → Prop
  | none => True
  | some R => ∀ r ∈ R, ValidLit m r

def ValidSt {V : Type} (st : St (Sum V ℕ)) : Prop :=
  ∀ C ∈ st.2, C.card ≤ 3 ∧ ValidCl st.1 C

def ValidMat {V : Type} {w : ℕ} (m : ℕ) (M : MatRep w (Sum V ℕ)) : Prop :=
  ∀ u v, ValidFailR m (M u v)

lemma ValidLit.mono {V : Type} {m1 m2 : ℕ} (h : m1 ≤ m2) {l : Lit (Sum V ℕ)}
    (hl : ValidLit m1 l) : ValidLit m2 l := fun k hk => Nat.lt_of_lt_of_le (hl k hk) h

lemma ValidLit.negL {V : Type} {m : ℕ} {l : Lit (Sum V ℕ)}
    (hl : ValidLit m l) : ValidLit m (negL l) := fun k hk => hl k hk

lemma ValidCl.mono {V : Type} {m1 m2 : ℕ} (h : m1 ≤ m2) {C : Cl (Sum V ℕ)}
    (hC : ValidCl m1 C) : ValidCl m2 C := fun l hl => (hC l hl).mono h

lemma ValidFailR.mono {V : Type} {m1 m2 : ℕ} (h : m1 ≤ m2) {R : FailR (Sum V ℕ)}
    (hR : ValidFailR m1 R) : ValidFailR m2 R := by
  cases R with
  | none => trivial
  | some L => exact fun r hr => (hR r hr).mono h

lemma ValidMat.mono {V : Type} {w m1 m2 : ℕ} (h : m1 ≤ m2) {M : MatRep w (Sum V ℕ)}
    (hM : ValidMat m1 M) : ValidMat m2 M := fun u v => (hM u v).mono h

lemma eval_lit_congr {V : Type} {m : ℕ} {a : V → Bool} {aux1 aux2 : ℕ → Bool}
    (hagree : ∀ k < m, aux1 k = aux2 k) {l : Lit (Sum V ℕ)} (hl : ValidLit m l) :
    Sum.elim a aux1 l.1 = Sum.elim a aux2 l.1 := by
  cases hx : l.1 with
  | inl v => rfl
  | inr k => exact hagree k (hl k hx)

lemma Fails_congr {V : Type} {m : ℕ} {a : V → Bool} {aux1 aux2 : ℕ → Bool}
    (hagree : ∀ k < m, aux1 k = aux2 k) {R : FailR (Sum V ℕ)} (hR : ValidFailR m R) :
    Fails (Sum.elim a aux1) R ↔ Fails (Sum.elim a aux2) R := by
  cases R with
  | none => rfl
  | some L =>
    constructor
    · rintro ⟨r, hr, hsat⟩
      exact ⟨r, hr, by rw [← eval_lit_congr hagree (hR r hr)]; exact hsat⟩
    · rintro ⟨r, hr, hsat⟩
      exact ⟨r, hr, by rw [eval_lit_congr hagree (hR r hr)]; exact hsat⟩

lemma ClauseSat_congr {V : Type} {m : ℕ} {a : V → Bool} {aux1 aux2 : ℕ → Bool}
    (hagree : ∀ k < m, aux1 k = aux2 k) {C : Cl (Sum V ℕ)} (hC : ValidCl m C) :
    PEqualNP.ProofComplexity.ClauseSat (Sum.elim a aux1) C ↔
    PEqualNP.ProofComplexity.ClauseSat (Sum.elim a aux2) C := by
  constructor
  · rintro ⟨l, hl, hsat⟩
    exact ⟨l, hl, by rw [← eval_lit_congr hagree (hC l hl)]; exact hsat⟩
  · rintro ⟨l, hl, hsat⟩
    exact ⟨l, hl, by rw [eval_lit_congr hagree (hC l hl)]; exact hsat⟩

lemma KnownFail.mono {W : Type} {K1 K2 : Set (Lit W)} (h : K1 ⊆ K2) {R : FailR W}
    (hR : KnownFail K1 R) : KnownFail K2 R := by
  cases R with
  | none => trivial
  | some L =>
    rcases hR with ⟨r, hr, hK⟩
    exact ⟨r, hr, h hK⟩

def andFail {W : Type} : FailR W → FailR W → FailR W
  | none, _ => none
  | _, none => none
  | some R1, some R2 => some (R1 ++ R2)

lemma Fails_andFail {W : Type} (α : W → Bool) (A B : FailR W) :
    Fails α (andFail A B) ↔ Fails α A ∨ Fails α B := by
  cases A with
  | none => cases B <;> simp [andFail, Fails]
  | some R1 =>
    cases B with
    | none => simp [andFail, Fails]
    | some R2 =>
      simp only [andFail, Fails, List.mem_append]
      constructor
      · rintro ⟨r, hr | hr, h⟩
        · exact Or.inl ⟨r, hr, h⟩
        · exact Or.inr ⟨r, hr, h⟩
      · rintro (⟨r, hr, h⟩ | ⟨r, hr, h⟩)
        · exact ⟨r, Or.inl hr, h⟩
        · exact ⟨r, Or.inr hr, h⟩

lemma KnownFail_andFail {W : Type} (K : Set (Lit W)) (A B : FailR W) :
    KnownFail K (andFail A B) ↔ KnownFail K A ∨ KnownFail K B := by
  cases A with
  | none => cases B <;> simp [andFail, KnownFail]
  | some R1 =>
    cases B with
    | none => simp [andFail, KnownFail]
    | some R2 =>
      simp only [andFail, KnownFail, List.mem_append]
      constructor
      · rintro ⟨r, hr | hr, h⟩
        · exact Or.inl ⟨r, hr, h⟩
        · exact Or.inr ⟨r, hr, h⟩
      · rintro (⟨r, hr, h⟩ | ⟨r, hr, h⟩)
        · exact ⟨r, Or.inl hr, h⟩
        · exact ⟨r, Or.inr hr, h⟩

lemma rLen_andFail {W : Type} (A B : FailR W) : rLen (andFail A B) ≤ rLen A + rLen B := by
  cases A <;> cases B <;> simp [andFail, rLen]

lemma ValidFailR_andFail {V : Type} {m : ℕ} {A B : FailR (Sum V ℕ)}
    (hA : ValidFailR m A) (hB : ValidFailR m B) : ValidFailR m (andFail A B) := by
  cases A with
  | none => cases B <;> trivial
  | some R1 =>
    cases B with
    | none => trivial
    | some R2 =>
      intro r hr
      rcases List.mem_append.1 hr with hr | hr
      · exact hA r hr
      · exact hB r hr

def orClauses {W : Type} [DecidableEq W] (A B : FailR W) (out : Option (Lit W)) : List (Cl W) :=
  match A, B, out with
  | none, none, none => [∅]
  | none, none, some l => [{l}]
  | none, some R2, none => R2.map (fun r2 => {negL r2})
  | none, some R2, some l => R2.map (fun r2 => {negL r2, l})
  | some R1, none, none => R1.map (fun r1 => {negL r1})
  | some R1, none, some l => R1.map (fun r1 => {negL r1, l})
  | some R1, some R2, none => R1.flatMap (fun r1 => R2.map (fun r2 => {negL r1, negL r2}))
  | some R1, some R2, some l => R1.flatMap (fun r1 => R2.map (fun r2 => {negL r1, negL r2, l}))

lemma orClauses_card {W : Type} [DecidableEq W] (A B : FailR W) (out : Option (Lit W)) :
    ∀ C ∈ orClauses A B out, C.card ≤ 3 := by
  cases A <;> cases B <;> cases out <;> simp only [orClauses, List.mem_singleton, List.mem_map, List.mem_flatMap]
  · intro C hC; rw [hC]; simp
  · intro C hC; rw [hC]; simp
  · rintro C ⟨r2, _, rfl⟩; simp
  · rintro C ⟨r2, _, rfl⟩; exact Finset.card_le_two.trans (by omega)
  · rintro C ⟨r1, _, rfl⟩; simp
  · rintro C ⟨r1, _, rfl⟩; exact Finset.card_le_two.trans (by omega)
  · rintro C ⟨r1, _, r2, _, rfl⟩; exact Finset.card_le_two.trans (by omega)
  · rintro C ⟨r1, _, r2, _, rfl⟩; exact Finset.card_le_three

lemma orClauses_length {W : Type} [DecidableEq W] (A B : FailR W) (out : Option (Lit W)) :
    (orClauses A B out).length ≤ max 1 (rLen A) * max 1 (rLen B) := by
  cases A with
  | none =>
    cases B with
    | none => cases out <;> simp [orClauses, rLen]
    | some R2 => cases out <;> simp [orClauses, rLen]
  | some R1 =>
    cases B with
    | none => cases out <;> simp [orClauses, rLen]
    | some R2 =>
      cases out <;>
        (simp only [orClauses, rLen];
         rw [list_flatMap_length_const _ _ R2.length (fun _ _ => by simp)];
         exact Nat.mul_le_mul (le_max_right 1 R1.length) (le_max_right 1 R2.length))

lemma orClauses_valid {V : Type} [DecidableEq V] {m : ℕ} {A B : FailR (Sum V ℕ)}
    {out : Option (Lit (Sum V ℕ))}
    (hA : ValidFailR m A) (hB : ValidFailR m B)
    (hout : ∀ l, out = some l → ValidLit m l) :
    ∀ C ∈ orClauses A B out, ValidCl m C := by
  cases A with
  | none =>
    cases B with
    | none =>
      cases out with
      | none => simp [orClauses, ValidCl]
      | some l =>
        intro C hC x hx
        simp only [orClauses, List.mem_singleton] at hC
        subst hC
        simp only [Finset.mem_singleton] at hx
        subst hx
        exact hout _ rfl
    | some R2 =>
      cases out with
      | none =>
        rintro C hC x hx
        simp only [orClauses, List.mem_map] at hC
        rcases hC with ⟨r2, hr2, rfl⟩
        simp only [Finset.mem_singleton] at hx
        subst hx
        exact (hB r2 hr2).negL
      | some l =>
        rintro C hC x hx
        simp only [orClauses, List.mem_map] at hC
        rcases hC with ⟨r2, hr2, rfl⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact (hB r2 hr2).negL
        · exact hout _ rfl
  | some R1 =>
    cases B with
    | none =>
      cases out with
      | none =>
        rintro C hC x hx
        simp only [orClauses, List.mem_map] at hC
        rcases hC with ⟨r1, hr1, rfl⟩
        simp only [Finset.mem_singleton] at hx
        subst hx
        exact (hA r1 hr1).negL
      | some l =>
        rintro C hC x hx
        simp only [orClauses, List.mem_map] at hC
        rcases hC with ⟨r1, hr1, rfl⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact (hA r1 hr1).negL
        · exact hout _ rfl
    | some R2 =>
      cases out with
      | none =>
        rintro C hC x hx
        simp only [orClauses, List.mem_flatMap, List.mem_map] at hC
        rcases hC with ⟨r1, hr1, r2, hr2, rfl⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact (hA r1 hr1).negL
        · exact (hB r2 hr2).negL
      | some l =>
        rintro C hC x hx
        simp only [orClauses, List.mem_flatMap, List.mem_map] at hC
        rcases hC with ⟨r1, hr1, r2, hr2, rfl⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl
        · exact (hA r1 hr1).negL
        · exact (hB r2 hr2).negL
        · exact hout _ rfl

lemma negL_sat_iff {W : Type} (α : W → Bool) (r : Lit W) :
    α (negL r).1 = (negL r).2 ↔ α r.1 ≠ r.2 := by
  simp only [negL_fst, negL_snd]
  cases α r.1 <;> cases r.2 <;> simp

lemma orClauses_sat_some {W : Type} [DecidableEq W] (α : W → Bool)
    (A B : FailR W) (l : Lit W) :
    (∀ C ∈ orClauses A B (some l), PEqualNP.ProofComplexity.ClauseSat α C) ↔
    ((Fails α A ∧ Fails α B) → α l.1 = l.2) := by
  cases A with
  | none =>
    cases B with
    | none =>
      simp only [orClauses, List.mem_singleton, forall_eq, PEqualNP.ProofComplexity.ClauseSat,
        Finset.mem_singleton, exists_eq_left, Fails, and_self, true_imp_iff]
    | some R2 =>
      simp only [orClauses, List.mem_map, Fails, true_and, PEqualNP.ProofComplexity.ClauseSat]
      constructor
      · rintro h ⟨r2, hr2, h2⟩
        obtain ⟨u, hu, hsat⟩ := h {negL r2, l} ⟨r2, hr2, rfl⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl
        · exact absurd h2 ((negL_sat_iff α r2).1 hsat)
        · exact hsat
      · intro h C hC
        rcases hC with ⟨r2, hr2, rfl⟩
        by_cases h2 : α r2.1 = r2.2
        · exact ⟨l, by simp, h ⟨r2, hr2, h2⟩⟩
        · exact ⟨negL r2, by simp, (negL_sat_iff α r2).2 h2⟩
  | some R1 =>
    cases B with
    | none =>
      simp only [orClauses, List.mem_map, Fails, and_true, PEqualNP.ProofComplexity.ClauseSat]
      constructor
      · rintro h ⟨r1, hr1, h1⟩
        obtain ⟨u, hu, hsat⟩ := h {negL r1, l} ⟨r1, hr1, rfl⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl
        · exact absurd h1 ((negL_sat_iff α r1).1 hsat)
        · exact hsat
      · intro h C hC
        rcases hC with ⟨r1, hr1, rfl⟩
        by_cases h1 : α r1.1 = r1.2
        · exact ⟨l, by simp, h ⟨r1, hr1, h1⟩⟩
        · exact ⟨negL r1, by simp, (negL_sat_iff α r1).2 h1⟩
    | some R2 =>
      simp only [orClauses, List.mem_flatMap, List.mem_map, Fails, PEqualNP.ProofComplexity.ClauseSat]
      constructor
      · rintro h ⟨⟨r1, hr1, h1⟩, ⟨r2, hr2, h2⟩⟩
        obtain ⟨u, hu, hsat⟩ := h {negL r1, negL r2, l} ⟨r1, hr1, r2, hr2, rfl⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl
        · exact absurd h1 ((negL_sat_iff α r1).1 hsat)
        · exact absurd h2 ((negL_sat_iff α r2).1 hsat)
        · exact hsat
      · intro h C hC
        rcases hC with ⟨r1, hr1, r2, hr2, rfl⟩
        by_cases h1 : α r1.1 = r1.2
        · by_cases h2 : α r2.1 = r2.2
          · exact ⟨l, by simp, h ⟨⟨r1, hr1, h1⟩, ⟨r2, hr2, h2⟩⟩⟩
          · exact ⟨negL r2, by simp, (negL_sat_iff α r2).2 h2⟩
        · exact ⟨negL r1, by simp, (negL_sat_iff α r1).2 h1⟩

lemma orClauses_sat_none {W : Type} [DecidableEq W] (α : W → Bool) (A B : FailR W) :
    (∀ C ∈ orClauses A B none, PEqualNP.ProofComplexity.ClauseSat α C) ↔
    ¬ (Fails α A ∧ Fails α B) := by
  cases A with
  | none =>
    cases B with
    | none =>
      simp [orClauses, PEqualNP.ProofComplexity.ClauseSat, Fails]
    | some R2 =>
      simp only [orClauses, List.mem_map, Fails, true_and, PEqualNP.ProofComplexity.ClauseSat]
      constructor
      · rintro h ⟨r2, hr2, h2⟩
        obtain ⟨u, hu, hsat⟩ := h {negL r2} ⟨r2, hr2, rfl⟩
        simp only [Finset.mem_singleton] at hu
        subst hu
        exact (negL_sat_iff α r2).1 hsat h2
      · intro h C hC
        rcases hC with ⟨r2, hr2, rfl⟩
        refine ⟨negL r2, by simp, (negL_sat_iff α r2).2 ?_⟩
        intro h2
        exact h ⟨r2, hr2, h2⟩
  | some R1 =>
    cases B with
    | none =>
      simp only [orClauses, List.mem_map, Fails, and_true, PEqualNP.ProofComplexity.ClauseSat]
      constructor
      · rintro h ⟨r1, hr1, h1⟩
        obtain ⟨u, hu, hsat⟩ := h {negL r1} ⟨r1, hr1, rfl⟩
        simp only [Finset.mem_singleton] at hu
        subst hu
        exact (negL_sat_iff α r1).1 hsat h1
      · intro h C hC
        rcases hC with ⟨r1, hr1, rfl⟩
        refine ⟨negL r1, by simp, (negL_sat_iff α r1).2 ?_⟩
        intro h1
        exact h ⟨r1, hr1, h1⟩
    | some R2 =>
      simp only [orClauses, List.mem_flatMap, List.mem_map, Fails, PEqualNP.ProofComplexity.ClauseSat]
      constructor
      · rintro h ⟨⟨r1, hr1, h1⟩, ⟨r2, hr2, h2⟩⟩
        obtain ⟨u, hu, hsat⟩ := h {negL r1, negL r2} ⟨r1, hr1, r2, hr2, rfl⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl
        · exact (negL_sat_iff α r1).1 hsat h1
        · exact (negL_sat_iff α r2).1 hsat h2
      · intro h C hC
        rcases hC with ⟨r1, hr1, r2, hr2, rfl⟩
        by_cases h1 : α r1.1 = r1.2
        · refine ⟨negL r2, by simp, (negL_sat_iff α r2).2 ?_⟩
          intro h2
          exact h ⟨⟨r1, hr1, h1⟩, ⟨r2, hr2, h2⟩⟩
        · exact ⟨negL r1, by simp, (negL_sat_iff α r1).2 h1⟩

lemma orClauses_upStep_some {W : Type} [DecidableEq W] {F : Finset (Cl W)} {K : Set (Lit W)}
    {A B : FailR W} {l : Lit W}
    (hF : ∀ C ∈ orClauses A B (some l), C ∈ F) (hA : KnownFail K A) (hB : KnownFail K B) :
    l ∈ upStep F K := by
  cases A with
  | none =>
    cases B with
    | none =>
      refine Or.inr ⟨{l}, hF {l} (by simp [orClauses]), by simp, ?_⟩
      intro o ho hne
      simp only [Finset.mem_singleton] at ho
      exact absurd ho hne
    | some R2 =>
      rcases hB with ⟨r2, hr2, hK2⟩
      refine Or.inr ⟨{negL r2, l}, hF _ (List.mem_map.2 ⟨r2, hr2, rfl⟩), by simp, ?_⟩
      intro o ho hne
      simp only [Finset.mem_insert, Finset.mem_singleton] at ho
      rcases ho with rfl | rfl
      · rwa [negL_negL]
      · exact absurd rfl hne
  | some R1 =>
    cases B with
    | none =>
      rcases hA with ⟨r1, hr1, hK1⟩
      refine Or.inr ⟨{negL r1, l}, hF _ (List.mem_map.2 ⟨r1, hr1, rfl⟩), by simp, ?_⟩
      intro o ho hne
      simp only [Finset.mem_insert, Finset.mem_singleton] at ho
      rcases ho with rfl | rfl
      · rwa [negL_negL]
      · exact absurd rfl hne
    | some R2 =>
      rcases hA with ⟨r1, hr1, hK1⟩
      rcases hB with ⟨r2, hr2, hK2⟩
      refine Or.inr ⟨{negL r1, negL r2, l},
        hF _ (List.mem_flatMap.2 ⟨r1, hr1, List.mem_map.2 ⟨r2, hr2, rfl⟩⟩), by simp, ?_⟩
      intro o ho hne
      simp only [Finset.mem_insert, Finset.mem_singleton] at ho
      rcases ho with rfl | rfl | rfl
      · rwa [negL_negL]
      · rwa [negL_negL]
      · exact absurd rfl hne

lemma orClauses_upStep_none {W : Type} [DecidableEq W] {F : Finset (Cl W)} {K : Set (Lit W)}
    {A B : FailR W}
    (hF : ∀ C ∈ orClauses A B none, C ∈ F) (hA : KnownFail K A) (hB : KnownFail K B) :
    ∃ D ∈ F, ∀ l ∈ D, negL l ∈ K := by
  cases A with
  | none =>
    cases B with
    | none =>
      exact ⟨∅, hF ∅ (by simp [orClauses]), by simp⟩
    | some R2 =>
      rcases hB with ⟨r2, hr2, hK2⟩
      refine ⟨{negL r2}, hF _ (List.mem_map.2 ⟨r2, hr2, rfl⟩), ?_⟩
      intro l hl
      simp only [Finset.mem_singleton] at hl
      rw [hl, negL_negL]
      exact hK2
  | some R1 =>
    cases B with
    | none =>
      rcases hA with ⟨r1, hr1, hK1⟩
      refine ⟨{negL r1}, hF _ (List.mem_map.2 ⟨r1, hr1, rfl⟩), ?_⟩
      intro l hl
      simp only [Finset.mem_singleton] at hl
      rw [hl, negL_negL]
      exact hK1
    | some R2 =>
      rcases hA with ⟨r1, hr1, hK1⟩
      rcases hB with ⟨r2, hr2, hK2⟩
      refine ⟨{negL r1, negL r2},
        hF _ (List.mem_flatMap.2 ⟨r1, hr1, List.mem_map.2 ⟨r2, hr2, rfl⟩⟩), ?_⟩
      intro l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl
      · rwa [negL_negL]
      · rwa [negL_negL]

def orAlloc {V : Type} [DecidableEq V] (A B : FailR (Sum V ℕ))
    (st : St (Sum V ℕ)) : St (Sum V ℕ) × FailR (Sum V ℕ) :=
  match A, B with
  | none, none => (st, none)
  | _, _ =>
    let q := st.1
    let cs := orClauses A B (some (Sum.inr q, false))
    ((q + 1, cs ++ st.2), some [(Sum.inr q, false)])

lemma orAlloc_props {V : Type} [DecidableEq V] (A B : FailR (Sum V ℕ)) (st : St (Sum V ℕ))
    (hst : ValidSt st) (hA : ValidFailR st.1 A) (hB : ValidFailR st.1 B) :
    let res := orAlloc A B st
    ValidSt res.1 ∧ st.1 ≤ res.1.1 ∧ (∀ C ∈ st.2, C ∈ res.1.2) ∧
    ValidFailR res.1.1 res.2 ∧ rLen res.2 ≤ 1 ∧
    res.1.1 ≤ st.1 + 1 ∧ res.1.2.length ≤ st.2.length + max 1 (rLen A) * max 1 (rLen B) := by
  have hlen := orClauses_length A B (some (Sum.inr st.1, false))
  cases A <;> cases B
  · dsimp only [orAlloc]
    refine ⟨hst, le_rfl, fun _ h => h, trivial, by simp [rLen], by omega, by simp⟩
  all_goals
    dsimp only [orAlloc]
    refine ⟨?_, by omega, fun C hC => List.mem_append_right _ hC, ?_, by simp [rLen], by omega, ?_⟩
    · intro C hC
      rcases List.mem_append.1 hC with hC | hC
      · refine ⟨orClauses_card _ _ _ C hC, orClauses_valid (hA.mono (by omega)) (hB.mono (by omega)) ?_ C hC⟩
        intro l hl
        have := Option.some.inj hl
        subst this
        intro k hk
        have hk' := Sum.inr.inj hk
        omega
      · exact ⟨(hst C hC).1, (hst C hC).2.mono (by omega)⟩
    · intro r hr k hk
      simp only [List.mem_singleton] at hr
      subst hr
      have hk' := Sum.inr.inj hk
      omega
    · simp only [List.length_append]
      omega

lemma orAlloc_ext {V : Type} [DecidableEq V] (A B : FailR (Sum V ℕ)) (st : St (Sum V ℕ))
    (hst : ValidSt st) (hA : ValidFailR st.1 A) (hB : ValidFailR st.1 B)
    (a : V → Bool) (aux0 : ℕ → Bool)
    (hsat : ∀ C ∈ st.2, PEqualNP.ProofComplexity.ClauseSat (Sum.elim a aux0) C) :
    let res := orAlloc A B st
    ∃ aux1 : ℕ → Bool,
      (∀ k < st.1, aux1 k = aux0 k) ∧
      (∀ C ∈ res.1.2, PEqualNP.ProofComplexity.ClauseSat (Sum.elim a aux1) C) ∧
      (Fails (Sum.elim a aux1) res.2 ↔ Fails (Sum.elim a aux0) A ∧ Fails (Sum.elim a aux0) B) := by
  classical
  let failAB : Bool := decide (Fails (Sum.elim a aux0) A ∧ Fails (Sum.elim a aux0) B)
  let aux1 : ℕ → Bool := fun k => if k = st.1 then !failAB else aux0 k
  have hagree : ∀ k < st.1, aux1 k = aux0 k := fun k hk => by simp [aux1, Nat.ne_of_lt hk]
  cases A <;> cases B
  · exact ⟨aux0, fun _ _ => rfl, hsat, by simp [orAlloc, Fails]⟩
  all_goals
    dsimp only [orAlloc]
    refine ⟨aux1, hagree, ?_, ?_⟩
    · intro C hC
      rcases List.mem_append.1 hC with hC | hC
      · refine (orClauses_sat_some (Sum.elim a aux1) _ _ (Sum.inr st.1, false)).2 ?_ C hC
        intro hF
        rw [Fails_congr hagree hA, Fails_congr hagree hB] at hF
        change aux1 st.1 = false
        simp [aux1, failAB, hF]
      · exact (ClauseSat_congr hagree (hst C hC).2).2 (hsat C hC)
    · have hl : Fails (Sum.elim a aux1) (some [(Sum.inr st.1, false)]) ↔ aux1 st.1 = false := by
        simp [Fails]
      rw [hl]
      simp only [aux1, ↓reduceIte, Bool.not_eq_false', failAB, decide_eq_true_eq]

lemma orAlloc_sound {V : Type} [DecidableEq V] (A B : FailR (Sum V ℕ)) (st : St (Sum V ℕ))
    (α : Sum V ℕ → Bool)
    (hsat : ∀ C ∈ (orAlloc A B st).1.2, PEqualNP.ProofComplexity.ClauseSat α C)
    (hA : Fails α A) (hB : Fails α B) :
    Fails α (orAlloc A B st).2 := by
  cases A <;> cases B
  · trivial
  all_goals
    dsimp only [orAlloc] at hsat ⊢
    have h1 : ∀ C ∈ orClauses _ _ (some (Sum.inr st.1, false)),
        PEqualNP.ProofComplexity.ClauseSat α C := fun C hC => hsat C (List.mem_append_left _ hC)
    have h2 := (orClauses_sat_some α _ _ (Sum.inr st.1, false)).1 h1 ⟨hA, hB⟩
    exact ⟨(Sum.inr st.1, false), List.mem_singleton.2 rfl, h2⟩

lemma orAlloc_up {V : Type} [DecidableEq V] (A B : FailR (Sum V ℕ)) (st : St (Sum V ℕ))
    {F : Finset (Cl (Sum V ℕ))} {K : Set (Lit (Sum V ℕ))}
    (hF : ∀ C ∈ (orAlloc A B st).1.2, C ∈ F) (hA : KnownFail K A) (hB : KnownFail K B) :
    KnownFail (upStep F K) (orAlloc A B st).2 := by
  cases A <;> cases B
  · trivial
  all_goals
    dsimp only [orAlloc] at hF ⊢
    have h1 : ∀ C ∈ orClauses _ _ (some (Sum.inr st.1, false)), C ∈ F :=
      fun C hC => hF C (List.mem_append_left _ hC)
    exact ⟨(Sum.inr st.1, false), List.mem_singleton.2 rfl, orClauses_upStep_some h1 hA hB⟩

def foldBool {V : Type} [DecidableEq V] :
    (k : ℕ) → ((Fin k → Bool) → FailR (Sum V ℕ)) → St (Sum V ℕ) →
    St (Sum V ℕ) × FailR (Sum V ℕ)
  | 0, g, st => (st, g Fin.elim0)
  | k + 1, g, st =>
    let p0 := foldBool k (fun s => g (Fin.cons false s)) st
    let p1 := foldBool k (fun s => g (Fin.cons true s)) p0.1
    orAlloc p0.2 p1.2 p1.1

lemma foldBool_props {V : Type} [DecidableEq V] (B : ℕ) (hB : 1 ≤ B) :
    ∀ (k : ℕ) (g : (Fin k → Bool) → FailR (Sum V ℕ)) (st : St (Sum V ℕ)),
      ValidSt st → (∀ s, ValidFailR st.1 (g s)) → (∀ s, rLen (g s) ≤ B) →
      let res := foldBool k g st
      ValidSt res.1 ∧ st.1 ≤ res.1.1 ∧ (∀ C ∈ st.2, C ∈ res.1.2) ∧
      ValidFailR res.1.1 res.2 ∧ rLen res.2 ≤ (if k = 0 then B else 1) ∧
      res.1.1 ≤ st.1 + (2 ^ k - 1) ∧
      res.1.2.length ≤ st.2.length + (if k = 0 then 0 else 2 ^ (k - 1) * B * B + (2 ^ (k - 1) - 1))
  | 0, g, st, hst, hgV, hgL => by
    dsimp only [foldBool]
    refine ⟨hst, le_rfl, fun _ h => h, hgV Fin.elim0, by simpa using hgL Fin.elim0, by simp, by simp⟩
  | k + 1, g, st, hst, hgV, hgL => by
    dsimp only [foldBool]
    set p0 := foldBool k (fun s => g (Fin.cons false s)) st
    set p1 := foldBool k (fun s => g (Fin.cons true s)) p0.1
    have hp0 := foldBool_props B hB k (fun s => g (Fin.cons false s)) st hst
      (fun s => hgV _) (fun s => hgL _)
    have hp1 := foldBool_props B hB k (fun s => g (Fin.cons true s)) p0.1 hp0.1
      (fun s => (hgV _).mono hp0.2.1) (fun s => hgL _)
    have hor := orAlloc_props p0.2 p1.2 p1.1 hp1.1 (hp0.2.2.2.1.mono hp1.2.1) hp1.2.2.2.1
    refine ⟨hor.1, hp0.2.1.trans (hp1.2.1.trans hor.2.1),
      fun C hC => hor.2.2.1 C (hp1.2.2.1 C (hp0.2.2.1 C hC)),
      hor.2.2.2.1, by simpa using hor.2.2.2.2.1, ?_, ?_⟩
    · have h0 : p0.1.1 ≤ st.1 + (2 ^ k - 1) := hp0.2.2.2.2.2.1
      have h1 : p1.1.1 ≤ p0.1.1 + (2 ^ k - 1) := hp1.2.2.2.2.2.1
      have h2 : (orAlloc p0.2 p1.2 p1.1).1.1 ≤ p1.1.1 + 1 := hor.2.2.2.2.2.1
      have hpow : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by omega)
      have hpow2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      omega
    · cases k with
      | zero =>
        have hr0 : rLen p0.2 ≤ B := by simpa using hp0.2.2.2.2.1
        have hr1 : rLen p1.2 ≤ B := by simpa using hp1.2.2.2.2.1
        have hmul : max 1 (rLen p0.2) * max 1 (rLen p1.2) ≤ B * B :=
          Nat.mul_le_mul (max_le hB hr0) (max_le hB hr1)
        have hlen0 : p0.1.2.length ≤ st.2.length := by simpa using hp0.2.2.2.2.2.2
        have hlen1 : p1.1.2.length ≤ p0.1.2.length := by simpa using hp1.2.2.2.2.2.2
        have horl : (orAlloc p0.2 p1.2 p1.1).1.2.length ≤ p1.1.2.length + max 1 (rLen p0.2) * max 1 (rLen p1.2) :=
          hor.2.2.2.2.2.2
        simp only [pow_zero, one_mul, Nat.sub_self, add_zero, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
        omega
      | succ k' =>
        have hr0 : rLen p0.2 ≤ 1 := by simpa using hp0.2.2.2.2.1
        have hr1 : rLen p1.2 ≤ 1 := by simpa using hp1.2.2.2.2.1
        have hmul : max 1 (rLen p0.2) * max 1 (rLen p1.2) ≤ 1 := by
          have hm0 : max 1 (rLen p0.2) = 1 := max_eq_left hr0
          have hm1 : max 1 (rLen p1.2) = 1 := max_eq_left hr1
          rw [hm0, hm1]
        have hpow : 1 ≤ 2 ^ k' := Nat.one_le_pow k' 2 (by omega)
        have hpow2 : 2 ^ (k' + 1) = 2 * 2 ^ k' := by ring
        have hlen0 : p0.1.2.length ≤ st.2.length + (2 ^ k' * B * B + (2 ^ k' - 1)) := by
          simpa using hp0.2.2.2.2.2.2
        have hlen1 : p1.1.2.length ≤ p0.1.2.length + (2 ^ k' * B * B + (2 ^ k' - 1)) := by
          simpa using hp1.2.2.2.2.2.2
        have horl : (orAlloc p0.2 p1.2 p1.1).1.2.length ≤ p1.1.2.length + max 1 (rLen p0.2) * max 1 (rLen p1.2) :=
          hor.2.2.2.2.2.2
        simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
        have hBB : 2 ^ (k' + 1) * B * B = 2 * (2 ^ k' * B * B) := by rw [hpow2]; ring
        omega

lemma foldBool_valid {V : Type} [DecidableEq V] :
    ∀ (k : ℕ) (g : (Fin k → Bool) → FailR (Sum V ℕ)) (st : St (Sum V ℕ)),
      ValidSt st → (∀ s, ValidFailR st.1 (g s)) →
      let res := foldBool k g st
      ValidSt res.1 ∧ st.1 ≤ res.1.1 ∧ (∀ C ∈ st.2, C ∈ res.1.2) ∧
      ValidFailR res.1.1 res.2
  | 0, g, st, hst, hgV => ⟨hst, le_rfl, fun _ h => h, hgV Fin.elim0⟩
  | k + 1, g, st, hst, hgV => by
    dsimp only [foldBool]
    set p0 := foldBool k (fun s => g (Fin.cons false s)) st
    set p1 := foldBool k (fun s => g (Fin.cons true s)) p0.1
    have hp0 := foldBool_valid k (fun s => g (Fin.cons false s)) st hst (fun s => hgV _)
    have hp1 := foldBool_valid k (fun s => g (Fin.cons true s)) p0.1 hp0.1 (fun s => (hgV _).mono hp0.2.1)
    have hor := orAlloc_props p0.2 p1.2 p1.1 hp1.1 (hp0.2.2.2.mono hp1.2.1) hp1.2.2.2
    exact ⟨hor.1, hp0.2.1.trans (hp1.2.1.trans hor.2.1),
      fun C hC => hor.2.2.1 C (hp1.2.2.1 C (hp0.2.2.1 C hC)), hor.2.2.2.1⟩

lemma fin_cons_decomp {k : ℕ} (s : Fin (k + 1) → Bool) :
    s = Fin.cons (s 0) (fun i => s i.succ) := by
  funext j
  refine Fin.cases ?_ ?_ j
  · rfl
  · intro i; rfl

lemma foldBool_ext {V : Type} [DecidableEq V] :
    ∀ (k : ℕ) (g : (Fin k → Bool) → FailR (Sum V ℕ)) (st : St (Sum V ℕ)),
      ValidSt st → (∀ s, ValidFailR st.1 (g s)) →
      ∀ (a : V → Bool) (aux0 : ℕ → Bool),
        (∀ C ∈ st.2, PEqualNP.ProofComplexity.ClauseSat (Sum.elim a aux0) C) →
        let res := foldBool k g st
        ∃ aux1 : ℕ → Bool,
          (∀ j < st.1, aux1 j = aux0 j) ∧
          (∀ C ∈ res.1.2, PEqualNP.ProofComplexity.ClauseSat (Sum.elim a aux1) C) ∧
          (Fails (Sum.elim a aux1) res.2 ↔ ∀ s, Fails (Sum.elim a aux0) (g s))
  | 0, g, st, _, _, a, aux0, hsat => by
    refine ⟨aux0, fun _ _ => rfl, hsat, ?_⟩
    constructor
    · intro h s
      have hs : s = Fin.elim0 := funext (fun i => Fin.elim0 i)
      rwa [hs]
    · intro h; exact h Fin.elim0
  | k + 1, g, st, hst, hgV, a, aux0, hsat => by
    dsimp only [foldBool]
    set p0 := foldBool k (fun s => g (Fin.cons false s)) st
    set p1 := foldBool k (fun s => g (Fin.cons true s)) p0.1
    have hp0v := foldBool_valid k (fun s => g (Fin.cons false s)) st hst (fun s => hgV _)
    have hp1v := foldBool_valid k (fun s => g (Fin.cons true s)) p0.1 hp0v.1 (fun s => (hgV _).mono hp0v.2.1)
    obtain ⟨aux1, h1ag, h1sat, h1iff⟩ :=
      foldBool_ext k (fun s => g (Fin.cons false s)) st hst (fun s => hgV _) a aux0 hsat
    obtain ⟨aux2, h2ag, h2sat, h2iff⟩ :=
      foldBool_ext k (fun s => g (Fin.cons true s)) p0.1 hp0v.1 (fun s => (hgV _).mono hp0v.2.1) a aux1 h1sat
    obtain ⟨aux3, h3ag, h3sat, h3iff⟩ :=
      orAlloc_ext p0.2 p1.2 p1.1 hp1v.1 (hp0v.2.2.2.mono hp1v.2.1) hp1v.2.2.2 a aux2 h2sat
    have h20 : ∀ j < st.1, aux2 j = aux0 j := fun j hj => (h2ag j (Nat.lt_of_lt_of_le hj hp0v.2.1)).trans (h1ag j hj)
    have h30 : ∀ j < st.1, aux3 j = aux0 j := fun j hj =>
      (h3ag j (Nat.lt_of_lt_of_le hj (hp0v.2.1.trans hp1v.2.1))).trans (h20 j hj)
    refine ⟨aux3, h30, h3sat, ?_⟩
    rw [h3iff, Fails_congr h2ag hp0v.2.2.2, h1iff, h2iff]
    constructor
    · rintro ⟨hF, hT⟩ s
      rw [fin_cons_decomp s]
      cases s 0
      · exact hF (fun i => s i.succ)
      · exact (Fails_congr h1ag (hgV _)).1 (hT (fun i => s i.succ))
    · intro hAll
      exact ⟨fun s => hAll _, fun s => (Fails_congr h1ag (hgV _)).2 (hAll _)⟩

lemma foldBool_clauses_mono {V : Type} [DecidableEq V] :
    ∀ (k : ℕ) (g : (Fin k → Bool) → FailR (Sum V ℕ)) (st : St (Sum V ℕ)),
      ∀ C ∈ st.2, C ∈ (foldBool k g st).1.2
  | 0, _, _, _, hC => hC
  | k + 1, g, st, C, hC => by
    dsimp only [foldBool]
    set p0 := foldBool k (fun s => g (Fin.cons false s)) st
    set p1 := foldBool k (fun s => g (Fin.cons true s)) p0.1
    have h1 := foldBool_clauses_mono k (fun s => g (Fin.cons true s)) p0.1 C
      (foldBool_clauses_mono k (fun s => g (Fin.cons false s)) st C hC)
    cases p0.2 <;> cases p1.2
    · exact h1
    all_goals exact List.mem_append_right _ h1

lemma foldBool_sound {V : Type} [DecidableEq V] :
    ∀ (k : ℕ) (g : (Fin k → Bool) → FailR (Sum V ℕ)) (st : St (Sum V ℕ))
      (α : Sum V ℕ → Bool),
      (∀ C ∈ (foldBool k g st).1.2, PEqualNP.ProofComplexity.ClauseSat α C) →
      (∀ s, Fails α (g s)) → Fails α (foldBool k g st).2
  | 0, g, _, α, _, hall => hall Fin.elim0
  | k + 1, g, st, α, hsat, hall => by
    dsimp only [foldBool] at hsat ⊢
    set p0 := foldBool k (fun s => g (Fin.cons false s)) st
    set p1 := foldBool k (fun s => g (Fin.cons true s)) p0.1
    have horSub : ∀ C ∈ p1.1.2, C ∈ (orAlloc p0.2 p1.2 p1.1).1.2 := by
      cases p0.2 <;> cases p1.2 <;> intro C hC
      · exact hC
      all_goals exact List.mem_append_right _ hC
    have h0 := foldBool_sound k (fun s => g (Fin.cons false s)) st α
      (fun C hC => hsat C (horSub C (foldBool_clauses_mono k _ p0.1 C hC))) (fun s => hall _)
    have h1 := foldBool_sound k (fun s => g (Fin.cons true s)) p0.1 α
      (fun C hC => hsat C (horSub C hC)) (fun s => hall _)
    exact orAlloc_sound p0.2 p1.2 p1.1 α hsat h0 h1

lemma foldBool_up {V : Type} [DecidableEq V] :
    ∀ (k : ℕ) (g : (Fin k → Bool) → FailR (Sum V ℕ)) (st : St (Sum V ℕ))
      {F : Finset (Cl (Sum V ℕ))} {K : Set (Lit (Sum V ℕ))},
      (∀ C ∈ (foldBool k g st).1.2, C ∈ F) →
      (∀ s, KnownFail K (g s)) →
      KnownFail ((upStep F)^[k] K) (foldBool k g st).2
  | 0, g, _, _, _, _, hall => hall Fin.elim0
  | k + 1, g, st, F, K, hF, hall => by
    dsimp only [foldBool] at hF ⊢
    set p0 := foldBool k (fun s => g (Fin.cons false s)) st
    set p1 := foldBool k (fun s => g (Fin.cons true s)) p0.1
    have horSub : ∀ C ∈ p1.1.2, C ∈ (orAlloc p0.2 p1.2 p1.1).1.2 := by
      cases p0.2 <;> cases p1.2 <;> intro C hC
      · exact hC
      all_goals exact List.mem_append_right _ hC
    have h0 := foldBool_up k (fun s => g (Fin.cons false s)) st
      (fun C hC => hF C (horSub C (foldBool_clauses_mono k _ p0.1 C hC))) (fun s => hall _)
    have h1 := foldBool_up k (fun s => g (Fin.cons true s)) p0.1
      (fun C hC => hF C (horSub C hC)) (fun s => hall _)
    rw [Function.iterate_succ_apply']
    exact orAlloc_up p0.2 p1.2 p1.1 hF h0 h1

def unitCost (w' : ℕ) : ℕ := 27 * 8 ^ (w' + 1)

def foldDiag {V : Type} [DecidableEq V] (w' : ℕ)
    (g : State (w' + 1) → FailR (Sum V ℕ)) (out : Option (Lit (Sum V ℕ)))
    (st : St (Sum V ℕ)) : St (Sum V ℕ) :=
  let p0 := foldBool w' (fun s => g (Fin.cons false s)) st
  let p1 := foldBool w' (fun s => g (Fin.cons true s)) p0.1
  (p1.1.1, orClauses p0.2 p1.2 out ++ p1.1.2)

lemma foldDiag_props {V : Type} [DecidableEq V] (w' : ℕ)
    (g : State (w' + 1) → FailR (Sum V ℕ)) (out : Option (Lit (Sum V ℕ)))
    (st : St (Sum V ℕ))
    (hst : ValidSt st) (hgV : ∀ s, ValidFailR st.1 (g s)) (hgL : ∀ s, rLen (g s) ≤ 2)
    (hout : ∀ l, out = some l → ValidLit st.1 l) :
    let st' := foldDiag w' g out st
    ValidSt st' ∧ st.1 ≤ st'.1 ∧ (∀ C ∈ st.2, C ∈ st'.2) ∧
    stCost st' ≤ stCost st + unitCost w' := by
  dsimp only [foldDiag]
  set p0 := foldBool w' (fun s => g (Fin.cons false s)) st
  set p1 := foldBool w' (fun s => g (Fin.cons true s)) p0.1
  have hp0 := foldBool_props 2 (by omega) w' (fun s => g (Fin.cons false s)) st hst (fun s => hgV _) (fun s => hgL _)
  have hp1 := foldBool_props 2 (by omega) w' (fun s => g (Fin.cons true s)) p0.1 hp0.1
    (fun s => (hgV _).mono hp0.2.1) (fun s => hgL _)
  have hm01 : st.1 ≤ p1.1.1 := hp0.2.1.trans hp1.2.1
  refine ⟨?_, hm01, fun C hC => List.mem_append_right _ (hp1.2.2.1 C (hp0.2.2.1 C hC)), ?_⟩
  · intro C hC
    rcases List.mem_append.1 hC with hC | hC
    · exact ⟨orClauses_card _ _ _ C hC,
        orClauses_valid (hp0.2.2.2.1.mono hp1.2.1) hp1.2.2.2.1 (fun l hl => (hout l hl).mono hm01) C hC⟩
    · exact hp1.1 C hC
  · have hvars : p1.1.1 ≤ st.1 + 2 * 2 ^ w' := by
      have h1 : p0.1.1 ≤ st.1 + (2 ^ w' - 1) := hp0.2.2.2.2.2.1
      have h2 : p1.1.1 ≤ p0.1.1 + (2 ^ w' - 1) := hp1.2.2.2.2.2.1
      omega
    have hcl : (orClauses p0.2 p1.2 out ++ p1.1.2).length ≤ st.2.length + 5 * 2 ^ w' := by
      rw [List.length_append]
      have hor := orClauses_length p0.2 p1.2 out
      cases w' with
      | zero =>
        have hr0 : rLen p0.2 ≤ 2 := by simpa using hp0.2.2.2.2.1
        have hr1 : rLen p1.2 ≤ 2 := by simpa using hp1.2.2.2.2.1
        have hmul : max 1 (rLen p0.2) * max 1 (rLen p1.2) ≤ 4 :=
          Nat.mul_le_mul (max_le (by omega) hr0) (max_le (by omega) hr1)
        have hl0 : p0.1.2.length ≤ st.2.length := by simpa using hp0.2.2.2.2.2.2
        have hl1 : p1.1.2.length ≤ p0.1.2.length := by simpa using hp1.2.2.2.2.2.2
        simp only [pow_zero, mul_one]
        omega
      | succ w'' =>
        have hr0 : rLen p0.2 ≤ 1 := by simpa using hp0.2.2.2.2.1
        have hr1 : rLen p1.2 ≤ 1 := by simpa using hp1.2.2.2.2.1
        have hmul : max 1 (rLen p0.2) * max 1 (rLen p1.2) ≤ 1 := by
          have hm0 : max 1 (rLen p0.2) = 1 := max_eq_left hr0
          have hm1 : max 1 (rLen p1.2) = 1 := max_eq_left hr1
          rw [hm0, hm1]
        have hl0 : p0.1.2.length ≤ st.2.length + (2 ^ w'' * 2 * 2 + (2 ^ w'' - 1)) := by
          simpa using hp0.2.2.2.2.2.2
        have hl1 : p1.1.2.length ≤ p0.1.2.length + (2 ^ w'' * 2 * 2 + (2 ^ w'' - 1)) := by
          simpa using hp1.2.2.2.2.2.2
        have hpow : 1 ≤ 2 ^ w'' := Nat.one_le_pow w'' 2 (by omega)
        have hpow2 : 2 ^ (w'' + 1) = 2 * 2 ^ w'' := by ring
        omega
    have hpow8 : 2 ^ w' ≤ 8 ^ (w' + 1) := by
      calc 2 ^ w' ≤ 2 ^ (w' + 1) := Nat.pow_le_pow_right (by omega) (Nat.le_succ w')
        _ ≤ 8 ^ (w' + 1) := Nat.pow_le_pow_left (by omega) (w' + 1)
    simp only [stCost, unitCost]
    omega

lemma foldDiag_ext_none {V : Type} [DecidableEq V] (w' : ℕ)
    (g : State (w' + 1) → FailR (Sum V ℕ)) (st : St (Sum V ℕ))
    (hst : ValidSt st) (hgV : ∀ s, ValidFailR st.1 (g s))
    (a : V → Bool) (aux0 : ℕ → Bool)
    (hsat : ∀ C ∈ st.2, PEqualNP.ProofComplexity.ClauseSat (Sum.elim a aux0) C)
    (hex : ∃ s, ¬ Fails (Sum.elim a aux0) (g s)) :
    ∃ aux1 : ℕ → Bool,
      (∀ k < st.1, aux1 k = aux0 k) ∧
      (∀ C ∈ (foldDiag w' g none st).2, PEqualNP.ProofComplexity.ClauseSat (Sum.elim a aux1) C) := by
  dsimp only [foldDiag]
  set p0 := foldBool w' (fun s => g (Fin.cons false s)) st
  set p1 := foldBool w' (fun s => g (Fin.cons true s)) p0.1
  have hp0v := foldBool_valid w' (fun s => g (Fin.cons false s)) st hst (fun s => hgV _)
  obtain ⟨aux1, h1ag, h1sat, h1iff⟩ :=
    foldBool_ext w' (fun s => g (Fin.cons false s)) st hst (fun s => hgV _) a aux0 hsat
  obtain ⟨aux2, h2ag, h2sat, h2iff⟩ :=
    foldBool_ext w' (fun s => g (Fin.cons true s)) p0.1 hp0v.1 (fun s => (hgV _).mono hp0v.2.1) a aux1 h1sat
  have h20 : ∀ j < st.1, aux2 j = aux0 j := fun j hj => (h2ag j (Nat.lt_of_lt_of_le hj hp0v.2.1)).trans (h1ag j hj)
  refine ⟨aux2, h20, ?_⟩
  intro C hC
  rcases List.mem_append.1 hC with hC | hC
  · refine (orClauses_sat_none (Sum.elim a aux2) p0.2 p1.2).2 ?_ C hC
    rintro ⟨hF0, hF1⟩
    rw [Fails_congr h2ag hp0v.2.2.2, h1iff] at hF0
    rw [h2iff] at hF1
    rcases hex with ⟨s, hs⟩
    apply hs
    rw [fin_cons_decomp s]
    cases s 0
    · exact hF0 (fun i => s i.succ)
    · exact (Fails_congr h1ag (hgV _)).1 (hF1 (fun i => s i.succ))
  · exact h2sat C hC

lemma foldDiag_ext_some {V : Type} [DecidableEq V] (w' : ℕ)
    (g : State (w' + 1) → FailR (Sum V ℕ)) (l : Lit (Sum V ℕ)) (st : St (Sum V ℕ))
    (hst : ValidSt st) (hgV : ∀ s, ValidFailR st.1 (g s)) (hlV : ValidLit st.1 l)
    (a : V → Bool) (aux0 : ℕ → Bool)
    (hsat : ∀ C ∈ st.2, PEqualNP.ProofComplexity.ClauseSat (Sum.elim a aux0) C)
    (himp : (∀ s, Fails (Sum.elim a aux0) (g s)) → Sum.elim a aux0 l.1 = l.2) :
    ∃ aux1 : ℕ → Bool,
      (∀ k < st.1, aux1 k = aux0 k) ∧
      (∀ C ∈ (foldDiag w' g (some l) st).2, PEqualNP.ProofComplexity.ClauseSat (Sum.elim a aux1) C) := by
  dsimp only [foldDiag]
  set p0 := foldBool w' (fun s => g (Fin.cons false s)) st
  set p1 := foldBool w' (fun s => g (Fin.cons true s)) p0.1
  have hp0v := foldBool_valid w' (fun s => g (Fin.cons false s)) st hst (fun s => hgV _)
  obtain ⟨aux1, h1ag, h1sat, h1iff⟩ :=
    foldBool_ext w' (fun s => g (Fin.cons false s)) st hst (fun s => hgV _) a aux0 hsat
  obtain ⟨aux2, h2ag, h2sat, h2iff⟩ :=
    foldBool_ext w' (fun s => g (Fin.cons true s)) p0.1 hp0v.1 (fun s => (hgV _).mono hp0v.2.1) a aux1 h1sat
  have h20 : ∀ j < st.1, aux2 j = aux0 j := fun j hj => (h2ag j (Nat.lt_of_lt_of_le hj hp0v.2.1)).trans (h1ag j hj)
  refine ⟨aux2, h20, ?_⟩
  intro C hC
  rcases List.mem_append.1 hC with hC | hC
  · refine (orClauses_sat_some (Sum.elim a aux2) p0.2 p1.2 l).2 ?_ C hC
    rintro ⟨hF0, hF1⟩
    rw [Fails_congr h2ag hp0v.2.2.2, h1iff] at hF0
    rw [h2iff] at hF1
    rw [eval_lit_congr h20 hlV]
    apply himp
    intro s
    rw [fin_cons_decomp s]
    cases s 0
    · exact hF0 (fun i => s i.succ)
    · exact (Fails_congr h1ag (hgV _)).1 (hF1 (fun i => s i.succ))
  · exact h2sat C hC

lemma foldDiag_sound_none {V : Type} [DecidableEq V] (w' : ℕ)
    (g : State (w' + 1) → FailR (Sum V ℕ)) (st : St (Sum V ℕ))
    (α : Sum V ℕ → Bool)
    (hsat : ∀ C ∈ (foldDiag w' g none st).2, PEqualNP.ProofComplexity.ClauseSat α C) :
    ∃ s, ¬ Fails α (g s) := by
  by_contra hno
  push Not at hno
  dsimp only [foldDiag] at hsat
  set p0 := foldBool w' (fun s => g (Fin.cons false s)) st
  set p1 := foldBool w' (fun s => g (Fin.cons true s)) p0.1
  have h1 : ∀ C ∈ p1.1.2, PEqualNP.ProofComplexity.ClauseSat α C :=
    fun C hC => hsat C (List.mem_append_right _ hC)
  have h0 : ∀ C ∈ p0.1.2, PEqualNP.ProofComplexity.ClauseSat α C :=
    fun C hC => h1 C (foldBool_clauses_mono w' _ p0.1 C hC)
  have hF0 := foldBool_sound w' (fun s => g (Fin.cons false s)) st α h0 (fun s => hno _)
  have hF1 := foldBool_sound w' (fun s => g (Fin.cons true s)) p0.1 α h1 (fun s => hno _)
  have hnone := (orClauses_sat_none α p0.2 p1.2).1
    (fun C hC => hsat C (List.mem_append_left _ hC))
  exact hnone ⟨hF0, hF1⟩

lemma foldDiag_up_none {V : Type} [DecidableEq V] (w' : ℕ)
    (g : State (w' + 1) → FailR (Sum V ℕ)) (st : St (Sum V ℕ))
    {F : Finset (Cl (Sum V ℕ))} {K : Set (Lit (Sum V ℕ))}
    (hF : ∀ C ∈ (foldDiag w' g none st).2, C ∈ F)
    (hall : ∀ s, KnownFail K (g s)) :
    ∃ D ∈ F, ∀ l ∈ D, negL l ∈ (upStep F)^[w'] K := by
  dsimp only [foldDiag] at hF
  set p0 := foldBool w' (fun s => g (Fin.cons false s)) st
  set p1 := foldBool w' (fun s => g (Fin.cons true s)) p0.1
  have hF1 : ∀ C ∈ p1.1.2, C ∈ F := fun C hC => hF C (List.mem_append_right _ hC)
  have hF0 : ∀ C ∈ p0.1.2, C ∈ F := fun C hC => hF1 C (foldBool_clauses_mono w' _ p0.1 C hC)
  have hK0 := foldBool_up w' (fun s => g (Fin.cons false s)) st hF0 (fun s => hall _)
  have hK1 := foldBool_up w' (fun s => g (Fin.cons true s)) p0.1 hF1 (fun s => hall _)
  exact orClauses_upStep_none (fun C hC => hF C (List.mem_append_left _ hC)) hK0 hK1

lemma foldDiag_up_some {V : Type} [DecidableEq V] (w' : ℕ)
    (g : State (w' + 1) → FailR (Sum V ℕ)) (l : Lit (Sum V ℕ)) (st : St (Sum V ℕ))
    {F : Finset (Cl (Sum V ℕ))} {K : Set (Lit (Sum V ℕ))}
    (hF : ∀ C ∈ (foldDiag w' g (some l) st).2, C ∈ F)
    (hall : ∀ s, KnownFail K (g s)) :
    l ∈ (upStep F)^[w' + 1] K := by
  dsimp only [foldDiag] at hF
  set p0 := foldBool w' (fun s => g (Fin.cons false s)) st
  set p1 := foldBool w' (fun s => g (Fin.cons true s)) p0.1
  have hF1 : ∀ C ∈ p1.1.2, C ∈ F := fun C hC => hF C (List.mem_append_right _ hC)
  have hF0 : ∀ C ∈ p0.1.2, C ∈ F := fun C hC => hF1 C (foldBool_clauses_mono w' _ p0.1 C hC)
  have hK0 := foldBool_up w' (fun s => g (Fin.cons false s)) st hF0 (fun s => hall _)
  have hK1 := foldBool_up w' (fun s => g (Fin.cons true s)) p0.1 hF1 (fun s => hall _)
  rw [Function.iterate_succ_apply']
  exact orClauses_upStep_some (fun C hC => hF C (List.mem_append_left _ hC)) hK0 hK1

def joinPairs {V : Type} [DecidableEq V] (w' : ℕ)
    (L R : MatRep (w' + 1) (Sum V ℕ)) :
    List (State (w' + 1) × State (w' + 1)) →
    St (Sum V ℕ) → MatRep (w' + 1) (Sum V ℕ) →
    St (Sum V ℕ) × MatRep (w' + 1) (Sum V ℕ)
  | [], st, M => (st, M)
  | (u, v) :: rest, st, M =>
    let p := foldBool (w' + 1) (fun y => andFail (L u y) (R y v)) st
    let M' := fun u' v' => if u' = u ∧ v' = v then p.2 else M u' v'
    joinPairs w' L R rest p.1 M'

lemma joinPairs_not_mem {V : Type} [DecidableEq V] (w' : ℕ)
    (L R : MatRep (w' + 1) (Sum V ℕ)) :
    ∀ (ps : List (State (w' + 1) × State (w' + 1))) (st : St (Sum V ℕ)) (M : MatRep (w' + 1) (Sum V ℕ))
      (u v : State (w' + 1)), (u, v) ∉ ps → (joinPairs w' L R ps st M).2 u v = M u v
  | [], _, _, _, _, _ => rfl
  | (u0, v0) :: rest, st, M, u, v, hnot => by
    have hne : ¬ (u = u0 ∧ v = v0) := by
      rintro ⟨rfl, rfl⟩
      exact hnot (List.mem_cons_self ..)
    have hnotr : (u, v) ∉ rest := fun h => hnot (List.mem_cons_of_mem _ h)
    dsimp only [joinPairs]
    rw [joinPairs_not_mem w' L R rest _ _ u v hnotr]
    simp [hne]

lemma joinPairs_clauses_mono {V : Type} [DecidableEq V] (w' : ℕ)
    (L R : MatRep (w' + 1) (Sum V ℕ)) :
    ∀ (ps : List (State (w' + 1) × State (w' + 1))) (st : St (Sum V ℕ)) (M : MatRep (w' + 1) (Sum V ℕ)),
      ∀ C ∈ st.2, C ∈ (joinPairs w' L R ps st M).1.2
  | [], _, _, _, hC => hC
  | (u, v) :: rest, st, M, C, hC => by
    dsimp only [joinPairs]
    exact joinPairs_clauses_mono w' L R rest _ _ C (foldBool_clauses_mono (w' + 1) _ st C hC)

lemma joinPairs_props {V : Type} [DecidableEq V] (w' : ℕ)
    (L R : MatRep (w' + 1) (Sum V ℕ)) :
    ∀ (ps : List (State (w' + 1) × State (w' + 1))) (st : St (Sum V ℕ)) (M : MatRep (w' + 1) (Sum V ℕ)),
      ValidSt st → ValidMat st.1 L → ValidMat st.1 R → ValidMat st.1 M →
      (∀ u v, rLen (L u v) ≤ 2) → (∀ u v, rLen (R u v) ≤ 2) → (∀ u v, rLen (M u v) ≤ 1) →
      let res := joinPairs w' L R ps st M
      ValidSt res.1 ∧ st.1 ≤ res.1.1 ∧ (∀ C ∈ st.2, C ∈ res.1.2) ∧
      ValidMat res.1.1 res.2 ∧ (∀ u v, rLen (res.2 u v) ≤ 1) ∧
      res.1.1 ≤ st.1 + ps.length * 2 ^ (w' + 1) ∧
      res.1.2.length ≤ st.2.length + ps.length * (17 * 2 ^ w')
  | [], st, M, hst, _, _, hMV, _, _, hML => by
    dsimp only [joinPairs]
    exact ⟨hst, le_rfl, fun _ h => h, hMV, hML, by simp, by simp⟩
  | (u, v) :: rest, st, M, hst, hLV, hRV, hMV, hLL, hRL, hML => by
    dsimp only [joinPairs]
    set p := foldBool (w' + 1) (fun y => andFail (L u y) (R y v)) st
    set M' : MatRep (w' + 1) (Sum V ℕ) := fun u' v' => if u' = u ∧ v' = v then p.2 else M u' v'
    have hp := foldBool_props 4 (by omega) (w' + 1) (fun y => andFail (L u y) (R y v)) st hst
      (fun y => ValidFailR_andFail (hLV u y) (hRV y v))
      (fun y => (rLen_andFail (L u y) (R y v)).trans (Nat.add_le_add (hLL u y) (hRL y v)))
    have hM'V : ValidMat p.1.1 M' := by
      intro u' v'
      dsimp only [M']
      split_ifs
      · exact hp.2.2.2.1
      · exact (hMV u' v').mono hp.2.1
    have hM'L : ∀ u' v', rLen (M' u' v') ≤ 1 := by
      intro u' v'
      dsimp only [M']
      split_ifs
      · simpa using hp.2.2.2.2.1
      · exact hML u' v'
    have hrest := joinPairs_props w' L R rest p.1 M' hp.1 (hLV.mono hp.2.1) (hRV.mono hp.2.1) hM'V hLL hRL hM'L
    refine ⟨hrest.1, hp.2.1.trans hrest.2.1,
      fun C hC => hrest.2.2.1 C (hp.2.2.1 C hC),
      hrest.2.2.2.1, hrest.2.2.2.2.1, ?_, ?_⟩
    · have h1 : p.1.1 ≤ st.1 + (2 ^ (w' + 1) - 1) := hp.2.2.2.2.2.1
      have h2 : (joinPairs w' L R rest p.1 M').1.1 ≤ p.1.1 + rest.length * 2 ^ (w' + 1) := hrest.2.2.2.2.2.1
      have hpow : 1 ≤ 2 ^ (w' + 1) := Nat.one_le_pow (w' + 1) 2 (by omega)
      simp only [List.length_cons]
      have : (rest.length + 1) * 2 ^ (w' + 1) = rest.length * 2 ^ (w' + 1) + 2 ^ (w' + 1) := by ring
      omega
    · have h1 : p.1.2.length ≤ st.2.length + (2 ^ w' * 4 * 4 + (2 ^ w' - 1)) := by
        simpa using hp.2.2.2.2.2.2
      have h2 : (joinPairs w' L R rest p.1 M').1.2.length ≤ p.1.2.length + rest.length * (17 * 2 ^ w') :=
        hrest.2.2.2.2.2.2
      simp only [List.length_cons]
      have : (rest.length + 1) * (17 * 2 ^ w') = rest.length * (17 * 2 ^ w') + 17 * 2 ^ w' := by ring
      omega

lemma joinPairs_ext {V : Type} [DecidableEq V] (w' : ℕ)
    (L R : MatRep (w' + 1) (Sum V ℕ)) :
    ∀ (ps : List (State (w' + 1) × State (w' + 1))) (st : St (Sum V ℕ)) (M : MatRep (w' + 1) (Sum V ℕ)),
      ValidSt st → ValidMat st.1 L → ValidMat st.1 R →
      ∀ (a : V → Bool) (aux0 : ℕ → Bool),
        (∀ C ∈ st.2, PEqualNP.ProofComplexity.ClauseSat (Sum.elim a aux0) C) →
        let res := joinPairs w' L R ps st M
        ∃ aux1 : ℕ → Bool,
          (∀ k < st.1, aux1 k = aux0 k) ∧
          (∀ C ∈ res.1.2, PEqualNP.ProofComplexity.ClauseSat (Sum.elim a aux1) C) ∧
          (∀ u v, (u, v) ∈ ps →
            (Fails (Sum.elim a aux1) (res.2 u v) ↔
              ∀ y, Fails (Sum.elim a aux0) (L u y) ∨ Fails (Sum.elim a aux0) (R y v)))
  | [], st, _, _, _, _, _, aux0, hsat =>
    ⟨aux0, fun _ _ => rfl, hsat, fun _ _ h => by simp at h⟩
  | (u0, v0) :: rest, st, M, hst, hLV, hRV, a, aux0, hsat => by
    dsimp only [joinPairs]
    set p := foldBool (w' + 1) (fun y => andFail (L u0 y) (R y v0)) st
    set M' : MatRep (w' + 1) (Sum V ℕ) := fun u' v' => if u' = u0 ∧ v' = v0 then p.2 else M u' v'
    have hpv := foldBool_valid (w' + 1) (fun y => andFail (L u0 y) (R y v0)) st hst
      (fun y => ValidFailR_andFail (hLV u0 y) (hRV y v0))
    obtain ⟨aux1, h1ag, h1sat, h1iff⟩ :=
      foldBool_ext (w' + 1) (fun y => andFail (L u0 y) (R y v0)) st hst
        (fun y => ValidFailR_andFail (hLV u0 y) (hRV y v0)) a aux0 hsat
    obtain ⟨aux2, h2ag, h2sat, h2iff⟩ :=
      joinPairs_ext w' L R rest p.1 M' hpv.1 (hLV.mono hpv.2.1) (hRV.mono hpv.2.1) a aux1 h1sat
    have h20 : ∀ k < st.1, aux2 k = aux0 k := fun k hk => (h2ag k (Nat.lt_of_lt_of_le hk hpv.2.1)).trans (h1ag k hk)
    refine ⟨aux2, h20, h2sat, ?_⟩
    intro u v huv
    by_cases hmem : (u, v) ∈ rest
    · rw [h2iff u v hmem]
      constructor
      · intro h y
        rcases h y with hL | hR
        · exact Or.inl ((Fails_congr h1ag (hLV u y)).1 hL)
        · exact Or.inr ((Fails_congr h1ag (hRV y v)).1 hR)
      · intro h y
        rcases h y with hL | hR
        · exact Or.inl ((Fails_congr h1ag (hLV u y)).2 hL)
        · exact Or.inr ((Fails_congr h1ag (hRV y v)).2 hR)
    · have heq : (u, v) = (u0, v0) := by
        rcases List.mem_cons.1 huv with h | h
        · exact h
        · exact absurd h hmem
      rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
      rw [joinPairs_not_mem w' L R rest p.1 M' u v hmem]
      simp only [M', and_self, ↓reduceIte]
      rw [Fails_congr h2ag hpv.2.2.2, h1iff]
      constructor
      · intro h y; exact (Fails_andFail _ _ _).1 (h y)
      · intro h y; exact (Fails_andFail _ _ _).2 (h y)

lemma joinPairs_sound {V : Type} [DecidableEq V] (w' : ℕ)
    (L R : MatRep (w' + 1) (Sum V ℕ)) :
    ∀ (ps : List (State (w' + 1) × State (w' + 1))) (st : St (Sum V ℕ)) (M : MatRep (w' + 1) (Sum V ℕ))
      (α : Sum V ℕ → Bool),
      (∀ C ∈ (joinPairs w' L R ps st M).1.2, PEqualNP.ProofComplexity.ClauseSat α C) →
      ∀ u v, (u, v) ∈ ps → (∀ y, Fails α (L u y) ∨ Fails α (R y v)) →
        Fails α ((joinPairs w' L R ps st M).2 u v)
  | [], _, _, _, _, _, _, h, _ => by simp at h
  | (u0, v0) :: rest, st, M, α, hsat, u, v, huv, hall => by
    dsimp only [joinPairs] at hsat ⊢
    set p := foldBool (w' + 1) (fun y => andFail (L u0 y) (R y v0)) st
    set M' : MatRep (w' + 1) (Sum V ℕ) := fun u' v' => if u' = u0 ∧ v' = v0 then p.2 else M u' v'
    by_cases hmem : (u, v) ∈ rest
    · exact joinPairs_sound w' L R rest p.1 M' α hsat u v hmem hall
    · have heq : (u, v) = (u0, v0) := by
        rcases List.mem_cons.1 huv with h | h
        · exact h
        · exact absurd h hmem
      rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
      rw [joinPairs_not_mem w' L R rest p.1 M' u v hmem]
      simp only [M', and_self, ↓reduceIte]
      have hpsat : ∀ C ∈ p.1.2, PEqualNP.ProofComplexity.ClauseSat α C :=
        fun C hC => hsat C (joinPairs_clauses_mono w' L R rest p.1 M' C hC)
      exact foldBool_sound (w' + 1) (fun y => andFail (L u y) (R y v)) st α hpsat
        (fun y => (Fails_andFail α _ _).2 (hall y))

lemma joinPairs_up {V : Type} [DecidableEq V] (w' : ℕ)
    (L R : MatRep (w' + 1) (Sum V ℕ)) :
    ∀ (ps : List (State (w' + 1) × State (w' + 1))) (st : St (Sum V ℕ)) (M : MatRep (w' + 1) (Sum V ℕ))
      {F : Finset (Cl (Sum V ℕ))} {K : Set (Lit (Sum V ℕ))},
      (∀ C ∈ (joinPairs w' L R ps st M).1.2, C ∈ F) →
      ∀ u v, (u, v) ∈ ps → (∀ y, KnownFail K (L u y) ∨ KnownFail K (R y v)) →
        KnownFail ((upStep F)^[w' + 1] K) ((joinPairs w' L R ps st M).2 u v)
  | [], _, _, _, _, _, _, _, h, _ => by simp at h
  | (u0, v0) :: rest, st, M, F, K, hF, u, v, huv, hall => by
    dsimp only [joinPairs] at hF ⊢
    set p := foldBool (w' + 1) (fun y => andFail (L u0 y) (R y v0)) st
    set M' : MatRep (w' + 1) (Sum V ℕ) := fun u' v' => if u' = u0 ∧ v' = v0 then p.2 else M u' v'
    by_cases hmem : (u, v) ∈ rest
    · exact joinPairs_up w' L R rest p.1 M' hF u v hmem hall
    · have heq : (u, v) = (u0, v0) := by
        rcases List.mem_cons.1 huv with h | h
        · exact h
        · exact absurd h hmem
      rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
      rw [joinPairs_not_mem w' L R rest p.1 M' u v hmem]
      simp only [M', and_self, ↓reduceIte]
      have hpF : ∀ C ∈ p.1.2, C ∈ F :=
        fun C hC => hF C (joinPairs_clauses_mono w' L R rest p.1 M' C hC)
      exact foldBool_up (w' + 1) (fun y => andFail (L u y) (R y v)) st hpF
        (fun y => (KnownFail_andFail K _ _).2 (hall y))

def allPairs (w : ℕ) : List (State w × State w) :=
  (allTuples w).flatMap (fun u => (allTuples w).map (fun v => (u, v)))

lemma allPairs_length (w : ℕ) : (allPairs w).length = 4 ^ w := by
  unfold allPairs
  rw [list_flatMap_length_const _ _ (2 ^ w) (fun _ _ => by simp [allTuples_length])]
  rw [allTuples_length]
  calc 2 ^ w * 2 ^ w = (2 * 2) ^ w := (Nat.mul_pow 2 2 w).symm
    _ = 4 ^ w := by rfl

lemma mem_allPairs (w : ℕ) (u v : State w) : (u, v) ∈ allPairs w :=
  List.mem_flatMap.2 ⟨u, mem_allTuples w u, List.mem_map.2 ⟨v, mem_allTuples w v, rfl⟩⟩

def joinMat {V : Type} [DecidableEq V] (w' : ℕ)
    (L R : MatRep (w' + 1) (Sum V ℕ)) (st : St (Sum V ℕ)) :
    St (Sum V ℕ) × MatRep (w' + 1) (Sum V ℕ) :=
  joinPairs w' L R (allPairs (w' + 1)) st (fun _ _ => none)

lemma joinMat_props {V : Type} [DecidableEq V] (w' : ℕ)
    (L R : MatRep (w' + 1) (Sum V ℕ)) (st : St (Sum V ℕ))
    (hst : ValidSt st) (hLV : ValidMat st.1 L) (hRV : ValidMat st.1 R)
    (hLL : ∀ u v, rLen (L u v) ≤ 2) (hRL : ∀ u v, rLen (R u v) ≤ 2) :
    let res := joinMat w' L R st
    ValidSt res.1 ∧ st.1 ≤ res.1.1 ∧ (∀ C ∈ st.2, C ∈ res.1.2) ∧
    ValidMat res.1.1 res.2 ∧ (∀ u v, rLen (res.2 u v) ≤ 2) ∧
    stCost res.1 ≤ stCost st + unitCost w' := by
  have hp := joinPairs_props w' L R (allPairs (w' + 1)) st (fun _ _ => none)
    hst hLV hRV (fun _ _ => trivial) hLL hRL (fun _ _ => by simp [rLen])
  refine ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1,
    fun u v => (hp.2.2.2.2.1 u v).trans (by omega), ?_⟩
  have h1 : (joinMat w' L R st).1.1 ≤ st.1 + (allPairs (w' + 1)).length * 2 ^ (w' + 1) := hp.2.2.2.2.2.1
  have h2 : (joinMat w' L R st).1.2.length ≤ st.2.length + (allPairs (w' + 1)).length * (17 * 2 ^ w') :=
    hp.2.2.2.2.2.2
  rw [allPairs_length] at h1 h2
  have h48 : 4 ^ (w' + 1) * 2 ^ (w' + 1) = 8 ^ (w' + 1) := by
    calc 4 ^ (w' + 1) * 2 ^ (w' + 1) = (4 * 2) ^ (w' + 1) := (Nat.mul_pow 4 2 (w' + 1)).symm
      _ = 8 ^ (w' + 1) := rfl
  have h2w : 2 ^ (w' + 1) = 2 * 2 ^ w' := by ring
  have h42 : 2 * (4 ^ (w' + 1) * 2 ^ w') = 8 ^ (w' + 1) := by
    calc 2 * (4 ^ (w' + 1) * 2 ^ w') = 4 ^ (w' + 1) * (2 * 2 ^ w') := by ring
      _ = 4 ^ (w' + 1) * 2 ^ (w' + 1) := by rw [← h2w]
      _ = 8 ^ (w' + 1) := h48
  have h17 : 3 * (4 ^ (w' + 1) * (17 * 2 ^ w')) ≤ 26 * 8 ^ (w' + 1) := by
    have : 3 * (4 ^ (w' + 1) * (17 * 2 ^ w')) = 51 * (4 ^ (w' + 1) * 2 ^ w') := by ring
    omega
  simp only [stCost, unitCost]
  omega

def shiftCompat {w' : ℕ} (u v : State (w' + 1)) : Bool :=
  (List.finRange w').all (fun k => u ⟨k.val + 1, by omega⟩ == v ⟨k.val, by omega⟩)

lemma shiftCompat_iff {w' : ℕ} (u v : State (w' + 1)) :
    shiftCompat u v = true ↔ ∀ k : Fin w', u ⟨k.val + 1, by omega⟩ = v ⟨k.val, by omega⟩ := by
  simp [shiftCompat]

def edgeTuple {w' : ℕ} (u v : State (w' + 1)) : Fin (w' + 2) → Bool :=
  fun j => if h : j.val = 0 then u ⟨0, by omega⟩ else v ⟨j.val - 1, by omega⟩

def leafMat (n w' : ℕ) (i : Fin n) (modOpt : Option (TestSpec n (w' + 1)))
    [DecidableEq (Vis n (w' + 1))] : MatRep (w' + 1) (Sum (Vis n (w' + 1)) ℕ) :=
  fun u v =>
    if !shiftCompat u v then none
    else
      let t := edgeTuple u v
      match modOpt with
      | none =>
        some [(Sum.inl (Sum.inl i), !(u ⟨0, by omega⟩)),
              (Sum.inl (Sum.inr (i, t)), false)]
      | some (i', Sum.inl b) =>
        if i' = i then
          if u ⟨0, by omega⟩ == b then none
          else some [(Sum.inl (Sum.inr (i, t)), false)]
        else
          some [(Sum.inl (Sum.inl i), !(u ⟨0, by omega⟩)),
                (Sum.inl (Sum.inr (i, t)), false)]
      | some (i', Sum.inr t0) =>
        if i' = i ∧ t = t0 then none
        else
          some [(Sum.inl (Sum.inl i), !(u ⟨0, by omega⟩)),
                (Sum.inl (Sum.inr (i, t)), false)]

lemma leafMat_valid (n w' m : ℕ) (i : Fin n) (modOpt : Option (TestSpec n (w' + 1)))
    [DecidableEq (Vis n (w' + 1))] :
    ValidMat m (leafMat n w' i modOpt) ∧ ∀ u v, rLen (leafMat n w' i modOpt u v) ≤ 2 := by
  constructor
  · intro u v
    unfold leafMat
    split_ifs
    · trivial
    · cases modOpt with
      | none => intro r hr k hk; simp at hr; rcases hr with rfl | rfl <;> simp at hk
      | some T =>
        rcases T with ⟨i', spec⟩
        cases spec with
        | inl b =>
          dsimp only
          split_ifs
          · trivial
          · intro r hr k hk; simp at hr; rw [hr] at hk; simp at hk
          · intro r hr k hk; simp at hr; rcases hr with rfl | rfl <;> simp at hk
        | inr t0 =>
          dsimp only
          split_ifs
          · trivial
          · intro r hr k hk; simp at hr; rcases hr with rfl | rfl <;> simp at hk
  · intro u v
    unfold leafMat
    split_ifs
    · simp [rLen]
    · cases modOpt with
      | none => simp [rLen]
      | some T =>
        rcases T with ⟨i', spec⟩
        cases spec with
        | inl b => dsimp only; split_ifs <;> simp [rLen]
        | inr t0 => dsimp only; split_ifs <;> simp [rLen]

def StepOk (n w' : ℕ) (a : Vis n (w' + 1) → Bool) (modOpt : Option (TestSpec n (w' + 1)))
    (i : Fin n) (u v : State (w' + 1)) : Prop :=
  shiftCompat u v = true ∧
  match modOpt with
  | none => a (Sum.inl i) = u ⟨0, by omega⟩ ∧ a (Sum.inr (i, edgeTuple u v)) = true
  | some (i', Sum.inl b) =>
    if i' = i then u ⟨0, by omega⟩ = !b ∧ a (Sum.inr (i, edgeTuple u v)) = true
    else a (Sum.inl i) = u ⟨0, by omega⟩ ∧ a (Sum.inr (i, edgeTuple u v)) = true
  | some (i', Sum.inr t0) =>
    if i' = i then edgeTuple u v ≠ t0 ∧ a (Sum.inl i) = u ⟨0, by omega⟩ ∧ a (Sum.inr (i, edgeTuple u v)) = true
    else a (Sum.inl i) = u ⟨0, by omega⟩ ∧ a (Sum.inr (i, edgeTuple u v)) = true

lemma leafMat_Fails_iff (n w' : ℕ) (a : Vis n (w' + 1) → Bool) (aux : ℕ → Bool)
    (modOpt : Option (TestSpec n (w' + 1))) (i : Fin n) (u v : State (w' + 1))
    [DecidableEq (Vis n (w' + 1))] :
    Fails (Sum.elim a aux) (leafMat n w' i modOpt u v) ↔ ¬ StepOk n w' a modOpt i u v := by
  unfold leafMat StepOk
  cases hsc : shiftCompat u v
  · simp [Fails]
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, true_and]
    cases modOpt with
    | none =>
      simp only [Fails, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, Sum.elim_inl]
      cases a (Sum.inl i) <;> cases u ⟨0, by omega⟩ <;> cases a (Sum.inr (i, edgeTuple u v)) <;> simp
    | some T =>
      rcases T with ⟨i', spec⟩
      cases spec with
      | inl b =>
        by_cases hi : i' = i
        · simp only [hi, ↓reduceIte]
          cases hu : u ⟨0, by omega⟩ <;> cases b <;> cases hp : a (Sum.inr (i, edgeTuple u v)) <;>
            simp [Fails, hu, hp]
        · simp only [hi, ↓reduceIte, Fails, List.mem_cons, List.not_mem_nil, or_false,
            exists_eq_or_imp, exists_eq_left, Sum.elim_inl]
          cases a (Sum.inl i) <;> cases u ⟨0, by omega⟩ <;> cases a (Sum.inr (i, edgeTuple u v)) <;> simp
      | inr t0 =>
        by_cases hi : i' = i
        · by_cases ht : edgeTuple u v = t0
          · simp [hi, ht, Fails]
          · simp only [hi, ht, and_false, ↓reduceIte, ne_eq, not_false_eq_true, true_and,
              Fails, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left, Sum.elim_inl]
            cases a (Sum.inl i) <;> cases u ⟨0, by omega⟩ <;> cases a (Sum.inr (i, edgeTuple u v)) <;> simp
        · simp only [hi, false_and, ↓reduceIte, Fails, List.mem_cons, List.not_mem_nil, or_false,
            exists_eq_or_imp, exists_eq_left, Sum.elim_inl]
          cases a (Sum.inl i) <;> cases u ⟨0, by omega⟩ <;> cases a (Sum.inr (i, edgeTuple u v)) <;> simp

def StepPoss (n w' : ℕ) (ρ : Vis n (w' + 1) → Option Bool) (modOpt : Option (TestSpec n (w' + 1)))
    (i : Fin n) (u v : State (w' + 1)) : Prop :=
  shiftCompat u v = true ∧
  match modOpt with
  | none => ρ (Sum.inl i) ≠ some (!(u ⟨0, by omega⟩)) ∧ ρ (Sum.inr (i, edgeTuple u v)) ≠ some false
  | some (i', Sum.inl b) =>
    if i' = i then u ⟨0, by omega⟩ = !b ∧ ρ (Sum.inr (i, edgeTuple u v)) ≠ some false
    else ρ (Sum.inl i) ≠ some (!(u ⟨0, by omega⟩)) ∧ ρ (Sum.inr (i, edgeTuple u v)) ≠ some false
  | some (i', Sum.inr t0) =>
    if i' = i then edgeTuple u v ≠ t0 ∧ ρ (Sum.inl i) ≠ some (!(u ⟨0, by omega⟩)) ∧ ρ (Sum.inr (i, edgeTuple u v)) ≠ some false
    else ρ (Sum.inl i) ≠ some (!(u ⟨0, by omega⟩)) ∧ ρ (Sum.inr (i, edgeTuple u v)) ≠ some false

lemma mem_seedOf_inl {V M : Type} (ρ : V → Option Bool) (v : V) (b : Bool) :
    ((Sum.inl v, b) : Lit (Sum V M)) ∈ seedOf ρ ↔ ρ v = some b := by
  constructor
  · rintro ⟨v', hv', hrv⟩
    have := Sum.inl.inj hv'
    subst this
    exact hrv
  · intro h; exact ⟨v, rfl, h⟩

lemma leafMat_KnownFail_iff (n w' : ℕ) (ρ : Vis n (w' + 1) → Option Bool)
    (modOpt : Option (TestSpec n (w' + 1))) (i : Fin n) (u v : State (w' + 1))
    [DecidableEq (Vis n (w' + 1))] :
    KnownFail (seedOf ρ) (leafMat n w' i modOpt u v) ↔ ¬ StepPoss n w' ρ modOpt i u v := by
  unfold leafMat StepPoss
  cases hsc : shiftCompat u v
  · simp [KnownFail]
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, true_and]
    cases modOpt with
    | none =>
      simp only [KnownFail, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
        exists_eq_left, mem_seedOf_inl]
      tauto
    | some T =>
      rcases T with ⟨i', spec⟩
      cases spec with
      | inl b =>
        by_cases hi : i' = i
        · simp only [hi, ↓reduceIte]
          cases hu : u ⟨0, by omega⟩ <;> cases b <;>
            simp [KnownFail, mem_seedOf_inl]
        · simp only [hi, ↓reduceIte, KnownFail, List.mem_cons, List.not_mem_nil, or_false,
            exists_eq_or_imp, exists_eq_left, mem_seedOf_inl]
          tauto
      | inr t0 =>
        by_cases hi : i' = i
        · by_cases ht : edgeTuple u v = t0
          · simp [hi, ht, KnownFail]
          · simp only [hi, ht, and_false, ↓reduceIte, ne_eq, not_false_eq_true, true_and,
              KnownFail, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
              exists_eq_left, mem_seedOf_inl]
            tauto
        · simp only [hi, false_and, ↓reduceIte, KnownFail, List.mem_cons, List.not_mem_nil, or_false,
            exists_eq_or_imp, exists_eq_left, mem_seedOf_inl]
          tauto

def PathOk (n w' : ℕ) (a : Vis n (w' + 1) → Bool) (modOpt : Option (TestSpec n (w' + 1))) :
    (lo len : ℕ) → lo + len ≤ n → State (w' + 1) → State (w' + 1) → Prop
  | _, 0, _, u, v => u = v
  | lo, len + 1, hhi, u, v =>
    ∃ y, StepOk n w' a modOpt ⟨lo, by omega⟩ u y ∧ PathOk n w' a modOpt (lo + 1) len (by omega) y v

lemma PathOk_one (n w' : ℕ) (a : Vis n (w' + 1) → Bool) (modOpt : Option (TestSpec n (w' + 1)))
    (lo : ℕ) (hhi : lo + 1 ≤ n) (u v : State (w' + 1)) :
    PathOk n w' a modOpt lo 1 hhi u v ↔ StepOk n w' a modOpt ⟨lo, by omega⟩ u v := by
  simp [PathOk]

lemma PathOk_congr_len (n w' : ℕ) (a : Vis n (w' + 1) → Bool) (modOpt : Option (TestSpec n (w' + 1)))
    (lo len1 len2 : ℕ) (hhi1 : lo + len1 ≤ n) (hhi2 : lo + len2 ≤ n) (hlen : len1 = len2)
    (u v : State (w' + 1)) :
    PathOk n w' a modOpt lo len1 hhi1 u v ↔ PathOk n w' a modOpt lo len2 hhi2 u v := by
  subst hlen; rfl

lemma PathOk_add (n w' : ℕ) (a : Vis n (w' + 1) → Bool) (modOpt : Option (TestSpec n (w' + 1))) :
    ∀ (l1 l2 lo : ℕ) (hhi : lo + (l1 + l2) ≤ n) (u v : State (w' + 1)),
      PathOk n w' a modOpt lo (l1 + l2) hhi u v ↔
      ∃ y, PathOk n w' a modOpt lo l1 (by omega) u y ∧ PathOk n w' a modOpt (lo + l1) l2 (by omega) y v
  | 0, l2, lo, hhi, u, v => by simp [PathOk]
  | l1 + 1, l2, lo, hhi, u, v => by
    have h1 : PathOk n w' a modOpt lo (l1 + 1 + l2) hhi u v ↔
        ∃ z, StepOk n w' a modOpt ⟨lo, by omega⟩ u z ∧
          PathOk n w' a modOpt (lo + 1) (l1 + l2) (by omega) z v :=
      PathOk_congr_len n w' a modOpt lo (l1 + 1 + l2) ((l1 + l2) + 1) hhi (by omega) (by omega) u v
    rw [h1]
    constructor
    · rintro ⟨z, hz, hrest⟩
      obtain ⟨y, hy1, hy2⟩ := (PathOk_add n w' a modOpt l1 l2 (lo + 1) (by omega) z v).1 hrest
      refine ⟨y, ⟨z, hz, hy1⟩, ?_⟩
      have hlo : lo + 1 + l1 = lo + (l1 + 1) := by omega
      simpa [hlo] using hy2
    · rintro ⟨y, ⟨z, hz, hy1⟩, hy2⟩
      refine ⟨z, hz, (PathOk_add n w' a modOpt l1 l2 (lo + 1) (by omega) z v).2 ⟨y, hy1, ?_⟩⟩
      have hlo : lo + 1 + l1 = lo + (l1 + 1) := by omega
      simpa [hlo] using hy2

lemma PathOk_out_of_range (n w' : ℕ) (a : Vis n (w' + 1) → Bool) (T : TestSpec n (w' + 1)) :
    ∀ (len lo : ℕ) (hhi : lo + len ≤ n),
      (T.1.val < lo ∨ lo + len ≤ T.1.val) →
      ∀ u v, PathOk n w' a (some T) lo len hhi u v ↔ PathOk n w' a none lo len hhi u v
  | 0, _, _, _, _, _ => Iff.rfl
  | len + 1, lo, hhi, hout, u, v => by
    have hne : T.1 ≠ ⟨lo, by omega⟩ := by
      intro h; have := congrArg Fin.val h; dsimp only at this; omega
    have hstep : ∀ y, StepOk n w' a (some T) ⟨lo, by omega⟩ u y ↔ StepOk n w' a none ⟨lo, by omega⟩ u y := by
      intro y
      rcases T with ⟨i', spec⟩
      cases spec <;> simp [StepOk, hne]
    simp only [PathOk]
    constructor
    · rintro ⟨y, hy1, hy2⟩
      exact ⟨y, (hstep y).1 hy1, (PathOk_out_of_range n w' a T len (lo + 1) (by omega) (by omega) y v).1 hy2⟩
    · rintro ⟨y, hy1, hy2⟩
      exact ⟨y, (hstep y).2 hy1, (PathOk_out_of_range n w' a T len (lo + 1) (by omega) (by omega) y v).2 hy2⟩

def PathPoss (n w' : ℕ) (ρ : Vis n (w' + 1) → Option Bool) (modOpt : Option (TestSpec n (w' + 1))) :
    (lo len : ℕ) → lo + len ≤ n → State (w' + 1) → State (w' + 1) → Prop
  | _, 0, _, u, v => u = v
  | lo, len + 1, hhi, u, v =>
    ∃ y, StepPoss n w' ρ modOpt ⟨lo, by omega⟩ u y ∧ PathPoss n w' ρ modOpt (lo + 1) len (by omega) y v

lemma PathPoss_one (n w' : ℕ) (ρ : Vis n (w' + 1) → Option Bool) (modOpt : Option (TestSpec n (w' + 1)))
    (lo : ℕ) (hhi : lo + 1 ≤ n) (u v : State (w' + 1)) :
    PathPoss n w' ρ modOpt lo 1 hhi u v ↔ StepPoss n w' ρ modOpt ⟨lo, by omega⟩ u v := by
  simp [PathPoss]

lemma PathPoss_congr_len (n w' : ℕ) (ρ : Vis n (w' + 1) → Option Bool) (modOpt : Option (TestSpec n (w' + 1)))
    (lo len1 len2 : ℕ) (hhi1 : lo + len1 ≤ n) (hhi2 : lo + len2 ≤ n) (hlen : len1 = len2)
    (u v : State (w' + 1)) :
    PathPoss n w' ρ modOpt lo len1 hhi1 u v ↔ PathPoss n w' ρ modOpt lo len2 hhi2 u v := by
  subst hlen; rfl

lemma PathPoss_add (n w' : ℕ) (ρ : Vis n (w' + 1) → Option Bool) (modOpt : Option (TestSpec n (w' + 1))) :
    ∀ (l1 l2 lo : ℕ) (hhi : lo + (l1 + l2) ≤ n) (u v : State (w' + 1)),
      PathPoss n w' ρ modOpt lo (l1 + l2) hhi u v ↔
      ∃ y, PathPoss n w' ρ modOpt lo l1 (by omega) u y ∧ PathPoss n w' ρ modOpt (lo + l1) l2 (by omega) y v
  | 0, l2, lo, hhi, u, v => by simp [PathPoss]
  | l1 + 1, l2, lo, hhi, u, v => by
    have h1 : PathPoss n w' ρ modOpt lo (l1 + 1 + l2) hhi u v ↔
        ∃ z, StepPoss n w' ρ modOpt ⟨lo, by omega⟩ u z ∧
          PathPoss n w' ρ modOpt (lo + 1) (l1 + l2) (by omega) z v :=
      PathPoss_congr_len n w' ρ modOpt lo (l1 + 1 + l2) ((l1 + l2) + 1) hhi (by omega) (by omega) u v
    rw [h1]
    constructor
    · rintro ⟨z, hz, hrest⟩
      obtain ⟨y, hy1, hy2⟩ := (PathPoss_add n w' ρ modOpt l1 l2 (lo + 1) (by omega) z v).1 hrest
      refine ⟨y, ⟨z, hz, hy1⟩, ?_⟩
      have hlo : lo + 1 + l1 = lo + (l1 + 1) := by omega
      simpa [hlo] using hy2
    · rintro ⟨y, ⟨z, hz, hy1⟩, hy2⟩
      refine ⟨z, hz, (PathPoss_add n w' ρ modOpt l1 l2 (lo + 1) (by omega) z v).2 ⟨y, hy1, ?_⟩⟩
      have hlo : lo + 1 + l1 = lo + (l1 + 1) := by omega
      simpa [hlo] using hy2

lemma PathPoss_out_of_range (n w' : ℕ) (ρ : Vis n (w' + 1) → Option Bool) (T : TestSpec n (w' + 1)) :
    ∀ (len lo : ℕ) (hhi : lo + len ≤ n),
      (T.1.val < lo ∨ lo + len ≤ T.1.val) →
      ∀ u v, PathPoss n w' ρ (some T) lo len hhi u v ↔ PathPoss n w' ρ none lo len hhi u v
  | 0, _, _, _, _, _ => Iff.rfl
  | len + 1, lo, hhi, hout, u, v => by
    have hne : T.1 ≠ ⟨lo, by omega⟩ := by
      intro h; have := congrArg Fin.val h; dsimp only at this; omega
    have hstep : ∀ y, StepPoss n w' ρ (some T) ⟨lo, by omega⟩ u y ↔ StepPoss n w' ρ none ⟨lo, by omega⟩ u y := by
      intro y
      rcases T with ⟨i', spec⟩
      cases spec <;> simp [StepPoss, hne]
    simp only [PathPoss]
    constructor
    · rintro ⟨y, hy1, hy2⟩
      exact ⟨y, (hstep y).1 hy1, (PathPoss_out_of_range n w' ρ T len (lo + 1) (by omega) (by omega) y v).1 hy2⟩
    · rintro ⟨y, hy1, hy2⟩
      exact ⟨y, (hstep y).2 hy1, (PathPoss_out_of_range n w' ρ T len (lo + 1) (by omega) (by omega) y v).2 hy2⟩

def joinTestList {V : Type} [DecidableEq V] {n : ℕ} (w' : ℕ)
    (mkL mkR : TestSpec n (w' + 1) → MatRep (w' + 1) (Sum V ℕ)) :
    List (TestSpec n (w' + 1)) →
    St (Sum V ℕ) → (TestSpec n (w' + 1) → MatRep (w' + 1) (Sum V ℕ)) →
    St (Sum V ℕ) × (TestSpec n (w' + 1) → MatRep (w' + 1) (Sum V ℕ))
  | [], st, mods => (st, mods)
  | T :: rest, st, mods =>
    let p := joinMat w' (mkL T) (mkR T) st
    let mods' := fun T' => if T' = T then p.2 else mods T'
    joinTestList w' mkL mkR rest p.1 mods'

lemma joinTestList_not_mem {V : Type} [DecidableEq V] {n : ℕ} (w' : ℕ)
    (mkL mkR : TestSpec n (w' + 1) → MatRep (w' + 1) (Sum V ℕ)) :
    ∀ (ts : List (TestSpec n (w' + 1))) (st : St (Sum V ℕ))
      (mods : TestSpec n (w' + 1) → MatRep (w' + 1) (Sum V ℕ)) (T : TestSpec n (w' + 1)),
      T ∉ ts → (joinTestList w' mkL mkR ts st mods).2 T = mods T
  | [], _, _, _, _ => rfl
  | T0 :: rest, st, mods, T, hnot => by
    have hne : T ≠ T0 := fun h => hnot (h ▸ List.mem_cons_self ..)
    have hnotr : T ∉ rest := fun h => hnot (List.mem_cons_of_mem _ h)
    dsimp only [joinTestList]
    rw [joinTestList_not_mem w' mkL mkR rest _ _ T hnotr]
    simp [hne]

lemma joinTestList_clauses_mono {V : Type} [DecidableEq V] {n : ℕ} (w' : ℕ)
    (mkL mkR : TestSpec n (w' + 1) → MatRep (w' + 1) (Sum V ℕ)) :
    ∀ (ts : List (TestSpec n (w' + 1))) (st : St (Sum V ℕ))
      (mods : TestSpec n (w' + 1) → MatRep (w' + 1) (Sum V ℕ)),
      ∀ C ∈ st.2, C ∈ (joinTestList w' mkL mkR ts st mods).1.2
  | [], _, _, _, hC => hC
  | T :: rest, st, mods, C, hC => by
    dsimp only [joinTestList]
    exact joinTestList_clauses_mono w' mkL mkR rest _ _ C
      (joinPairs_clauses_mono w' (mkL T) (mkR T) _ st _ C hC)

lemma joinTestList_props {V : Type} [DecidableEq V] {n : ℕ} (w' : ℕ)
    (mkL mkR : TestSpec n (w' + 1) → MatRep (w' + 1) (Sum V ℕ)) :
    ∀ (ts : List (TestSpec n (w' + 1))) (st : St (Sum V ℕ))
      (mods : TestSpec n (w' + 1) → MatRep (w' + 1) (Sum V ℕ)),
      ValidSt st →
      (∀ T ∈ ts, ValidMat st.1 (mkL T) ∧ ValidMat st.1 (mkR T) ∧
        (∀ u v, rLen (mkL T u v) ≤ 2) ∧ (∀ u v, rLen (mkR T u v) ≤ 2)) →
      let res := joinTestList w' mkL mkR ts st mods
      ValidSt res.1 ∧ st.1 ≤ res.1.1 ∧ (∀ C ∈ st.2, C ∈ res.1.2) ∧
      (∀ T ∈ ts, ValidMat res.1.1 (res.2 T) ∧ ∀ u v, rLen (res.2 T u v) ≤ 2) ∧
      stCost res.1 ≤ stCost st + ts.length * unitCost w'
  | [], st, _, hst, _ => by
    dsimp only [joinTestList]
    exact ⟨hst, le_rfl, fun _ h => h, fun _ h => by simp at h, by simp⟩
  | T0 :: rest, st, mods, hst, hts => by
    dsimp only [joinTestList]
    have hT0 := hts T0 (List.mem_cons_self ..)
    set p := joinMat w' (mkL T0) (mkR T0) st
    set mods' := fun T' => if T' = T0 then p.2 else mods T'
    have hp := joinMat_props w' (mkL T0) (mkR T0) st hst hT0.1 hT0.2.1 hT0.2.2.1 hT0.2.2.2
    have hrest := joinTestList_props w' mkL mkR rest p.1 mods' hp.1 (fun T hT =>
      let h := hts T (List.mem_cons_of_mem T0 hT)
      ⟨h.1.mono hp.2.1, h.2.1.mono hp.2.1, h.2.2.1, h.2.2.2⟩)
    refine ⟨hrest.1, hp.2.1.trans hrest.2.1,
      fun C hC => hrest.2.2.1 C (hp.2.2.1 C hC), ?_, ?_⟩
    · intro T hT
      by_cases hmem : T ∈ rest
      · exact hrest.2.2.2.1 T hmem
      · have heq : T = T0 := by
          rcases List.mem_cons.1 hT with rfl | h
          · rfl
          · exact absurd h hmem
        subst heq
        rw [joinTestList_not_mem w' mkL mkR rest p.1 mods' T hmem]
        simp only [mods', ↓reduceIte]
        exact ⟨hp.2.2.2.1.mono hrest.2.1, hp.2.2.2.2.1⟩
    · have h1 : stCost p.1 ≤ stCost st + unitCost w' := hp.2.2.2.2.2
      have h2 : stCost (joinTestList w' mkL mkR rest p.1 mods').1 ≤ stCost p.1 + rest.length * unitCost w' :=
        hrest.2.2.2.2
      simp only [List.length_cons]
      have : (rest.length + 1) * unitCost w' = rest.length * unitCost w' + unitCost w' := by ring
      omega

lemma joinPairs_valid {V : Type} [DecidableEq V] (w' : ℕ)
    (L R : MatRep (w' + 1) (Sum V ℕ)) :
    ∀ (ps : List (State (w' + 1) × State (w' + 1))) (st : St (Sum V ℕ)) (M : MatRep (w' + 1) (Sum V ℕ)),
      ValidSt st → ValidMat st.1 L → ValidMat st.1 R → ValidMat st.1 M →
      let res := joinPairs w' L R ps st M
      ValidSt res.1 ∧ st.1 ≤ res.1.1 ∧ (∀ C ∈ st.2, C ∈ res.1.2) ∧ ValidMat res.1.1 res.2
  | [], st, _, hst, _, _, hMV => ⟨hst, le_rfl, fun _ h => h, hMV⟩
  | (u, v) :: rest, st, M, hst, hLV, hRV, hMV => by
    dsimp only [joinPairs]
    set p := foldBool (w' + 1) (fun y => andFail (L u y) (R y v)) st
    set M' : MatRep (w' + 1) (Sum V ℕ) := fun u' v' => if u' = u ∧ v' = v then p.2 else M u' v'
    have hp := foldBool_valid (w' + 1) (fun y => andFail (L u y) (R y v)) st hst
      (fun y => ValidFailR_andFail (hLV u y) (hRV y v))
    have hM'V : ValidMat p.1.1 M' := by
      intro u' v'
      dsimp only [M']
      split_ifs
      · exact hp.2.2.2
      · exact (hMV u' v').mono hp.2.1
    have hrest := joinPairs_valid w' L R rest p.1 M' hp.1 (hLV.mono hp.2.1) (hRV.mono hp.2.1) hM'V
    exact ⟨hrest.1, hp.2.1.trans hrest.2.1, fun C hC => hrest.2.2.1 C (hp.2.2.1 C hC), hrest.2.2.2⟩

lemma joinTestList_ext {V : Type} [DecidableEq V] {n : ℕ} (w' : ℕ)
    (mkL mkR : TestSpec n (w' + 1) → MatRep (w' + 1) (Sum V ℕ)) :
    ∀ (ts : List (TestSpec n (w' + 1))) (st : St (Sum V ℕ))
      (mods : TestSpec n (w' + 1) → MatRep (w' + 1) (Sum V ℕ)),
      ValidSt st →
      (∀ T ∈ ts, ValidMat st.1 (mkL T) ∧ ValidMat st.1 (mkR T)) →
      ∀ (a : V → Bool) (aux0 : ℕ → Bool),
        (∀ C ∈ st.2, PEqualNP.ProofComplexity.ClauseSat (Sum.elim a aux0) C) →
        let res := joinTestList w' mkL mkR ts st mods
        ∃ aux1 : ℕ → Bool,
          (∀ k < st.1, aux1 k = aux0 k) ∧
          (∀ C ∈ res.1.2, PEqualNP.ProofComplexity.ClauseSat (Sum.elim a aux1) C) ∧
          (∀ T ∈ ts, ∀ u v,
            Fails (Sum.elim a aux1) (res.2 T u v) ↔
            ∀ y, Fails (Sum.elim a aux0) (mkL T u y) ∨ Fails (Sum.elim a aux0) (mkR T y v))
  | [], st, _, _, _, _, aux0, hsat =>
    ⟨aux0, fun _ _ => rfl, hsat, fun _ h => by simp at h⟩
  | T0 :: rest, st, mods, hst, hts, a, aux0, hsat => by
    dsimp only [joinTestList]
    have hT0 := hts T0 (List.mem_cons_self ..)
    set p := joinMat w' (mkL T0) (mkR T0) st
    set mods' := fun T' => if T' = T0 then p.2 else mods T'
    have hpv := joinPairs_valid w' (mkL T0) (mkR T0) (allPairs (w' + 1)) st (fun _ _ => none)
      hst hT0.1 hT0.2 (fun _ _ => trivial)
    obtain ⟨aux1, h1ag, h1sat, h1iff⟩ :=
      joinPairs_ext w' (mkL T0) (mkR T0) (allPairs (w' + 1)) st (fun _ _ => none)
        hst hT0.1 hT0.2 a aux0 hsat
    obtain ⟨aux2, h2ag, h2sat, h2iff⟩ :=
      joinTestList_ext w' mkL mkR rest p.1 mods' hpv.1
        (fun T hT => let h := hts T (List.mem_cons_of_mem T0 hT); ⟨h.1.mono hpv.2.1, h.2.mono hpv.2.1⟩)
        a aux1 h1sat
    have h20 : ∀ k < st.1, aux2 k = aux0 k := fun k hk => (h2ag k (Nat.lt_of_lt_of_le hk hpv.2.1)).trans (h1ag k hk)
    refine ⟨aux2, h20, h2sat, ?_⟩
    intro T hT u v
    by_cases hmem : T ∈ rest
    · rw [h2iff T hmem u v]
      have hT' := hts T hT
      constructor
      · intro h y
        rcases h y with hL | hR
        · exact Or.inl ((Fails_congr h1ag (hT'.1 u y)).1 hL)
        · exact Or.inr ((Fails_congr h1ag (hT'.2 y v)).1 hR)
      · intro h y
        rcases h y with hL | hR
        · exact Or.inl ((Fails_congr h1ag (hT'.1 u y)).2 hL)
        · exact Or.inr ((Fails_congr h1ag (hT'.2 y v)).2 hR)
    · have heq : T = T0 := by
        rcases List.mem_cons.1 hT with rfl | h
        · rfl
        · exact absurd h hmem
      subst heq
      rw [joinTestList_not_mem w' mkL mkR rest p.1 mods' T hmem]
      simp only [mods', ↓reduceIte]
      dsimp only [p, joinMat]
      rw [Fails_congr h2ag (hpv.2.2.2 u v), h1iff u v (mem_allPairs (w' + 1) u v)]

lemma joinTestList_up {V : Type} [DecidableEq V] {n : ℕ} (w' : ℕ)
    (mkL mkR : TestSpec n (w' + 1) → MatRep (w' + 1) (Sum V ℕ)) :
    ∀ (ts : List (TestSpec n (w' + 1))) (st : St (Sum V ℕ))
      (mods : TestSpec n (w' + 1) → MatRep (w' + 1) (Sum V ℕ))
      {F : Finset (Cl (Sum V ℕ))} {K : Set (Lit (Sum V ℕ))},
      (∀ C ∈ (joinTestList w' mkL mkR ts st mods).1.2, C ∈ F) →
      ∀ T ∈ ts, ∀ u v, (∀ y, KnownFail K (mkL T u y) ∨ KnownFail K (mkR T y v)) →
        KnownFail ((upStep F)^[w' + 1] K) ((joinTestList w' mkL mkR ts st mods).2 T u v)
  | [], _, _, _, _, _, _, h, _, _, _ => by simp at h
  | T0 :: rest, st, mods, F, K, hF, T, hT, u, v, hall => by
    dsimp only [joinTestList] at hF ⊢
    set p := joinMat w' (mkL T0) (mkR T0) st
    set mods' := fun T' => if T' = T0 then p.2 else mods T'
    by_cases hmem : T ∈ rest
    · exact joinTestList_up w' mkL mkR rest p.1 mods' hF T hmem u v hall
    · have heq : T = T0 := by
        rcases List.mem_cons.1 hT with rfl | h
        · rfl
        · exact absurd h hmem
      subst heq
      rw [joinTestList_not_mem w' mkL mkR rest p.1 mods' T hmem]
      simp only [mods', ↓reduceIte]
      have hpF : ∀ C ∈ p.1.2, C ∈ F :=
        fun C hC => hF C (joinTestList_clauses_mono w' mkL mkR rest p.1 mods' C hC)
      exact joinPairs_up w' (mkL T) (mkR T) (allPairs (w' + 1)) st (fun _ _ => none)
        hpF u v (mem_allPairs (w' + 1) u v) hall

def buildAll (n w' : ℕ) [DecidableEq (Vis n (w' + 1))] :
    (h lo len : ℕ) → (1 ≤ len) → (lo + len ≤ n) →
    St (Sum (Vis n (w' + 1)) ℕ) →
    St (Sum (Vis n (w' + 1)) ℕ) ×
      (MatRep (w' + 1) (Sum (Vis n (w' + 1)) ℕ) ×
        (TestSpec n (w' + 1) → MatRep (w' + 1) (Sum (Vis n (w' + 1)) ℕ)))
  | 0, lo, _, _, hhi, st =>
    (st, (leafMat n w' ⟨lo, by omega⟩ none, fun T => leafMat n w' ⟨lo, by omega⟩ (some T)))
  | h' + 1, lo, len, hlen, hhi, st =>
    if h1 : len ≤ 1 then
      (st, (leafMat n w' ⟨lo, by omega⟩ none, fun T => leafMat n w' ⟨lo, by omega⟩ (some T)))
    else
      let leftLen := len / 2
      let rightLen := len - leftLen
      let rL := buildAll n w' h' lo leftLen (by omega) (by omega) st
      let rR := buildAll n w' h' (lo + leftLen) rightLen (by omega) (by omega) rL.1
      let pM := joinMat w' rL.2.1 rR.2.1 rR.1
      let pL := joinTestList w' rL.2.2 (fun _ => rR.2.1)
        (rangeTests n (w' + 1) lo leftLen (by omega)) pM.1 (fun _ => pM.2)
      let pR := joinTestList w' (fun _ => rL.2.1) rR.2.2
        (rangeTests n (w' + 1) (lo + leftLen) rightLen (by omega)) pL.1 pL.2
      (pR.1, (pM.2, pR.2))

lemma buildAll_props (n w' : ℕ) [DecidableEq (Vis n (w' + 1))] :
    ∀ (h lo len : ℕ) (hlen : 1 ≤ len) (hhi : lo + len ≤ n) (st : St (Sum (Vis n (w' + 1)) ℕ)),
      ValidSt st →
      let res := buildAll n w' h lo len hlen hhi st
      ValidSt res.1 ∧ st.1 ≤ res.1.1 ∧ (∀ C ∈ st.2, C ∈ res.1.2) ∧
      ValidMat res.1.1 res.2.1 ∧ (∀ u v, rLen (res.2.1 u v) ≤ 2) ∧
      (∀ T, lo ≤ T.1.val → T.1.val < lo + len →
        ValidMat res.1.1 (res.2.2 T) ∧ ∀ u v, rLen (res.2.2 T u v) ≤ 2) ∧
      stCost res.1 ≤ stCost st + ((len - 1) + h * len * (2 + 2 ^ (w' + 2))) * unitCost w'
  | 0, lo, len, hlen, hhi, st, hst => by
    dsimp only [buildAll]
    have hl0 := leafMat_valid n w' st.1 ⟨lo, by omega⟩ none
    refine ⟨hst, le_rfl, fun _ h => h, hl0.1, hl0.2, ?_, Nat.le_add_right _ _⟩
    intro T _ _
    exact leafMat_valid n w' st.1 ⟨lo, by omega⟩ (some T)
  | h' + 1, lo, len, hlen, hhi, st, hst => by
    dsimp only [buildAll]
    split_ifs with h1
    · have hl0 := leafMat_valid n w' st.1 ⟨lo, by omega⟩ none
      refine ⟨hst, le_rfl, fun _ h => h, hl0.1, hl0.2, ?_, Nat.le_add_right _ _⟩
      intro T _ _
      exact leafMat_valid n w' st.1 ⟨lo, by omega⟩ (some T)
    · set leftLen := len / 2
      set rightLen := len - leftLen
      set rL := buildAll n w' h' lo leftLen (by omega) (by omega) st
      set rR := buildAll n w' h' (lo + leftLen) rightLen (by omega) (by omega) rL.1
      set pM := joinMat w' rL.2.1 rR.2.1 rR.1
      set tsL := rangeTests n (w' + 1) lo leftLen (by omega)
      set tsR := rangeTests n (w' + 1) (lo + leftLen) rightLen (by omega)
      set pL := joinTestList w' rL.2.2 (fun _ => rR.2.1) tsL pM.1 (fun _ => pM.2)
      set pR := joinTestList w' (fun _ => rL.2.1) rR.2.2 tsR pL.1 pL.2
      have hrL := buildAll_props n w' h' lo leftLen (by omega) (by omega) st hst
      have hrR := buildAll_props n w' h' (lo + leftLen) rightLen (by omega) (by omega) rL.1 hrL.1
      have hpM := joinMat_props w' rL.2.1 rR.2.1 rR.1 hrR.1
        (hrL.2.2.2.1.mono hrR.2.1) hrR.2.2.2.1 hrL.2.2.2.2.1 hrR.2.2.2.2.1
      have hpL := joinTestList_props w' rL.2.2 (fun _ => rR.2.1) tsL pM.1 (fun _ => pM.2) hpM.1
        (fun T hT => by
          have hmem := (mem_rangeTests n (w' + 1) lo leftLen (by omega) T).1 hT
          have h1' := hrL.2.2.2.2.2.1 T hmem.1 hmem.2
          exact ⟨h1'.1.mono (hrR.2.1.trans hpM.2.1), hrR.2.2.2.1.mono hpM.2.1, h1'.2, hrR.2.2.2.2.1⟩)
      have hpR := joinTestList_props w' (fun _ => rL.2.1) rR.2.2 tsR pL.1 pL.2 hpL.1
        (fun T hT => by
          have hmem := (mem_rangeTests n (w' + 1) (lo + leftLen) rightLen (by omega) T).1 hT
          have h2' := hrR.2.2.2.2.2.1 T hmem.1 hmem.2
          exact ⟨hrL.2.2.2.1.mono (hrR.2.1.trans (hpM.2.1.trans hpL.2.1)),
            h2'.1.mono (hpM.2.1.trans hpL.2.1), hrL.2.2.2.2.1, h2'.2⟩)
      have hm_le : st.1 ≤ pR.1.1 := hrL.2.1.trans (hrR.2.1.trans (hpM.2.1.trans (hpL.2.1.trans hpR.2.1)))
      refine ⟨hpR.1, hm_le,
        fun C hC => hpR.2.2.1 C (hpL.2.2.1 C (hpM.2.2.1 C (hrR.2.2.1 C (hrL.2.2.1 C hC)))),
        hpM.2.2.2.1.mono (hpL.2.1.trans hpR.2.1), hpM.2.2.2.2.1, ?_, ?_⟩
      · intro T hlo hhiT
        by_cases hlt : T.1.val < lo + leftLen
        · have hnotR : T ∉ tsR := by
            intro h
            have := (mem_rangeTests n (w' + 1) (lo + leftLen) rightLen (by omega) T).1 h
            omega
          have hinL : T ∈ tsL := (mem_rangeTests n (w' + 1) lo leftLen (by omega) T).2 ⟨hlo, hlt⟩
          rw [joinTestList_not_mem w' (fun _ => rL.2.1) rR.2.2 tsR pL.1 pL.2 T hnotR]
          have hL := hpL.2.2.2.1 T hinL
          exact ⟨hL.1.mono hpR.2.1, hL.2⟩
        · have hinR : T ∈ tsR :=
            (mem_rangeTests n (w' + 1) (lo + leftLen) rightLen (by omega) T).2 ⟨by omega, by omega⟩
          exact hpR.2.2.2.1 T hinR
      · have hcL := hrL.2.2.2.2.2.2
        have hcR := hrR.2.2.2.2.2.2
        have hcM := hpM.2.2.2.2.2
        have hcTL := hpL.2.2.2.2
        have hcTR := hpR.2.2.2.2
        have htsL : tsL.length = leftLen * (2 + 2 ^ (w' + 2)) := rangeTests_length n (w' + 1) lo leftLen (by omega)
        have htsR : tsR.length = rightLen * (2 + 2 ^ (w' + 2)) := rangeTests_length n (w' + 1) (lo + leftLen) rightLen (by omega)
        rw [htsL] at hcTL
        rw [htsR] at hcTR
        have hsum : leftLen + rightLen = len := by omega
        have hL1 : 1 ≤ leftLen := by omega
        have hR1 : 1 ≤ rightLen := by omega
        set K := 2 + 2 ^ (w' + 2)
        have hcoeff :
            ((leftLen - 1) + h' * leftLen * K) + ((rightLen - 1) + h' * rightLen * K) + 1 +
              leftLen * K + rightLen * K = (len - 1) + (h' + 1) * len * K := by
          have hsub : (leftLen - 1) + (rightLen - 1) + 1 = len - 1 := by omega
          have hmul : h' * leftLen * K + h' * rightLen * K + leftLen * K + rightLen * K =
              (h' + 1) * len * K := by
            rw [← hsum]; ring
          omega
        have hcost : stCost pR.1 ≤ stCost st +
            (((leftLen - 1) + h' * leftLen * K) + ((rightLen - 1) + h' * rightLen * K) + 1 +
              leftLen * K + rightLen * K) * unitCost w' := by
          nlinarith
        rwa [hcoeff] at hcost

lemma buildAll_ext (n w' : ℕ) [DecidableEq (Vis n (w' + 1))] :
    ∀ (h lo len : ℕ) (hlen : 1 ≤ len) (hhi : lo + len ≤ n) (hpow : len ≤ 2 ^ h)
      (st : St (Sum (Vis n (w' + 1)) ℕ)),
      ValidSt st →
      ∀ (a : Vis n (w' + 1) → Bool) (aux0 : ℕ → Bool),
        (∀ C ∈ st.2, PEqualNP.ProofComplexity.ClauseSat (Sum.elim a aux0) C) →
        let res := buildAll n w' h lo len hlen hhi st
        ∃ aux1 : ℕ → Bool,
          (∀ k < st.1, aux1 k = aux0 k) ∧
          (∀ C ∈ res.1.2, PEqualNP.ProofComplexity.ClauseSat (Sum.elim a aux1) C) ∧
          (∀ u v, Fails (Sum.elim a aux1) (res.2.1 u v) ↔ ¬ PathOk n w' a none lo len hhi u v) ∧
          (∀ T, lo ≤ T.1.val → T.1.val < lo + len →
            ∀ u v, Fails (Sum.elim a aux1) (res.2.2 T u v) ↔ ¬ PathOk n w' a (some T) lo len hhi u v)
  | 0, lo, len, hlen, hhi, hpow, st, _, a, aux0, hsat => by
    have hlen1 : len = 1 := by simp at hpow; omega
    subst hlen1
    dsimp only [buildAll]
    refine ⟨aux0, fun _ _ => rfl, hsat, ?_, ?_⟩
    · intro u v
      rw [PathOk_one, leafMat_Fails_iff]
    · intro T _ _ u v
      rw [PathOk_one, leafMat_Fails_iff]
  | h' + 1, lo, len, hlen, hhi, hpow, st, hst, a, aux0, hsat => by
    dsimp only [buildAll]
    split_ifs with h1
    · have hlen1 : len = 1 := by omega
      subst hlen1
      refine ⟨aux0, fun _ _ => rfl, hsat, ?_, ?_⟩
      · intro u v; rw [PathOk_one, leafMat_Fails_iff]
      · intro T _ _ u v; rw [PathOk_one, leafMat_Fails_iff]
    · set leftLen := len / 2
      set rightLen := len - leftLen
      have hpow2 : 2 ^ (h' + 1) = 2 * 2 ^ h' := by ring
      have hpowL : leftLen ≤ 2 ^ h' := by omega
      have hpowR : rightLen ≤ 2 ^ h' := by omega
      set rL := buildAll n w' h' lo leftLen (by omega) (by omega) st
      set rR := buildAll n w' h' (lo + leftLen) rightLen (by omega) (by omega) rL.1
      set pM := joinMat w' rL.2.1 rR.2.1 rR.1
      set tsL := rangeTests n (w' + 1) lo leftLen (by omega)
      set tsR := rangeTests n (w' + 1) (lo + leftLen) rightLen (by omega)
      set pL := joinTestList w' rL.2.2 (fun _ => rR.2.1) tsL pM.1 (fun _ => pM.2)
      set pR := joinTestList w' (fun _ => rL.2.1) rR.2.2 tsR pL.1 pL.2
      have hrLp := buildAll_props n w' h' lo leftLen (by omega) (by omega) st hst
      have hrRp := buildAll_props n w' h' (lo + leftLen) rightLen (by omega) (by omega) rL.1 hrLp.1
      have hpMp := joinMat_props w' rL.2.1 rR.2.1 rR.1 hrRp.1
        (hrLp.2.2.2.1.mono hrRp.2.1) hrRp.2.2.2.1 hrLp.2.2.2.2.1 hrRp.2.2.2.2.1
      have hpLp := joinTestList_props w' rL.2.2 (fun _ => rR.2.1) tsL pM.1 (fun _ => pM.2) hpMp.1
        (fun T hT => by
          have hmem := (mem_rangeTests n (w' + 1) lo leftLen (by omega) T).1 hT
          have h1' := hrLp.2.2.2.2.2.1 T hmem.1 hmem.2
          exact ⟨h1'.1.mono (hrRp.2.1.trans hpMp.2.1), hrRp.2.2.2.1.mono hpMp.2.1, h1'.2, hrRp.2.2.2.2.1⟩)
      obtain ⟨aux1, h1ag, h1sat, h1M, h1T⟩ :=
        buildAll_ext n w' h' lo leftLen (by omega) (by omega) hpowL st hst a aux0 hsat
      obtain ⟨aux2, h2ag, h2sat, h2M, h2T⟩ :=
        buildAll_ext n w' h' (lo + leftLen) rightLen (by omega) (by omega) hpowR rL.1 hrLp.1 a aux1 h1sat
      obtain ⟨aux3, h3ag, h3sat, h3M⟩ :=
        joinPairs_ext w' rL.2.1 rR.2.1 (allPairs (w' + 1)) rR.1 (fun _ _ => none)
          hrRp.1 (hrLp.2.2.2.1.mono hrRp.2.1) hrRp.2.2.2.1 a aux2 h2sat
      obtain ⟨aux4, h4ag, h4sat, h4T⟩ :=
        joinTestList_ext w' rL.2.2 (fun _ => rR.2.1) tsL pM.1 (fun _ => pM.2) hpMp.1
          (fun T hT => by
            have hmem := (mem_rangeTests n (w' + 1) lo leftLen (by omega) T).1 hT
            exact ⟨(hrLp.2.2.2.2.2.1 T hmem.1 hmem.2).1.mono (hrRp.2.1.trans hpMp.2.1),
              hrRp.2.2.2.1.mono hpMp.2.1⟩) a aux3 h3sat
      obtain ⟨aux5, h5ag, h5sat, h5T⟩ :=
        joinTestList_ext w' (fun _ => rL.2.1) rR.2.2 tsR pL.1 pL.2 hpLp.1
          (fun T hT => by
            have hmem := (mem_rangeTests n (w' + 1) (lo + leftLen) rightLen (by omega) T).1 hT
            exact ⟨hrLp.2.2.2.1.mono (hrRp.2.1.trans (hpMp.2.1.trans hpLp.2.1)),
              (hrRp.2.2.2.2.2.1 T hmem.1 hmem.2).1.mono (hpMp.2.1.trans hpLp.2.1)⟩) a aux4 h4sat
      have h54 : ∀ k < pM.1.1, aux5 k = aux3 k := fun k hk =>
        (h5ag k (Nat.lt_of_lt_of_le hk hpLp.2.1)).trans (h4ag k hk)
      have h42 : ∀ k < rR.1.1, aux4 k = aux2 k := fun k hk =>
        (h4ag k (Nat.lt_of_lt_of_le hk hpMp.2.1)).trans (h3ag k hk)
      have h31 : ∀ k < rL.1.1, aux3 k = aux1 k := fun k hk =>
        (h3ag k (Nat.lt_of_lt_of_le hk hrRp.2.1)).trans (h2ag k hk)
      have h41 : ∀ k < rL.1.1, aux4 k = aux1 k := fun k hk =>
        (h42 k (Nat.lt_of_lt_of_le hk hrRp.2.1)).trans (h2ag k hk)
      have h50 : ∀ k < st.1, aux5 k = aux0 k := fun k hk =>
        (h54 k (Nat.lt_of_lt_of_le hk (hrLp.2.1.trans (hrRp.2.1.trans hpMp.2.1)))).trans
          ((h31 k (Nat.lt_of_lt_of_le hk hrLp.2.1)).trans (h1ag k hk))
      have hsum : leftLen + rightLen = len := by omega
      refine ⟨aux5, h50, h5sat, ?_, ?_⟩
      · intro u v
        rw [Fails_congr h54 (hpMp.2.2.2.1 u v)]
        dsimp only [pM, joinMat]
        rw [h3M u v (mem_allPairs (w' + 1) u v)]
        have hPath : PathOk n w' a none lo len hhi u v ↔
            ∃ y, PathOk n w' a none lo leftLen (by omega) u y ∧
              PathOk n w' a none (lo + leftLen) rightLen (by omega) y v := by
          have := PathOk_add n w' a none leftLen rightLen lo (by omega) u v
          simpa [hsum] using this
        rw [hPath]
        push Not
        constructor
        · intro hall y
          rcases hall y with hL | hR
          · rw [Fails_congr h2ag (hrLp.2.2.2.1 u y), h1M u y] at hL
            exact fun h => absurd h hL
          · rw [h2M y v] at hR
            exact fun _ h => absurd h hR
        · intro hall y
          by_cases hL : PathOk n w' a none lo leftLen (by omega) u y
          · exact Or.inr ((h2M y v).2 (hall y hL))
          · exact Or.inl ((Fails_congr h2ag (hrLp.2.2.2.1 u y)).2 ((h1M u y).2 hL))
      · intro T hlo hhiT u v
        have hPath : PathOk n w' a (some T) lo len hhi u v ↔
            ∃ y, PathOk n w' a (some T) lo leftLen (by omega) u y ∧
              PathOk n w' a (some T) (lo + leftLen) rightLen (by omega) y v := by
          have := PathOk_add n w' a (some T) leftLen rightLen lo (by omega) u v
          simpa [hsum] using this
        rw [hPath]
        push Not
        by_cases hlt : T.1.val < lo + leftLen
        · have hnotR : T ∉ tsR := by
            intro h; have := (mem_rangeTests n (w' + 1) (lo + leftLen) rightLen (by omega) T).1 h; omega
          have hinL : T ∈ tsL := (mem_rangeTests n (w' + 1) lo leftLen (by omega) T).2 ⟨hlo, hlt⟩
          rw [joinTestList_not_mem w' (fun _ => rL.2.1) rR.2.2 tsR pL.1 pL.2 T hnotR]
          rw [Fails_congr h5ag ((hpLp.2.2.2.1 T hinL).1 u v), h4T T hinL u v]
          constructor
          · intro hall y hPL hPR
            rcases hall y with hL | hR
            · rw [Fails_congr h31 ((hrLp.2.2.2.2.2.1 T hlo hlt).1 u y), h1T T hlo hlt u y] at hL
              exact hL hPL
            · rw [Fails_congr h3ag (hrRp.2.2.2.1 y v), h2M y v] at hR
              exact hR ((PathOk_out_of_range n w' a T rightLen (lo + leftLen) (by omega) (Or.inl hlt) y v).1 hPR)
          · intro hall y
            by_cases hPL : PathOk n w' a (some T) lo leftLen (by omega) u y
            · refine Or.inr ((Fails_congr h3ag (hrRp.2.2.2.1 y v)).2 ((h2M y v).2 ?_))
              intro hPR
              exact hall y hPL ((PathOk_out_of_range n w' a T rightLen (lo + leftLen) (by omega) (Or.inl hlt) y v).2 hPR)
            · exact Or.inl ((Fails_congr h31 ((hrLp.2.2.2.2.2.1 T hlo hlt).1 u y)).2 ((h1T T hlo hlt u y).2 hPL))
        · have hge : lo + leftLen ≤ T.1.val := by omega
          have hhiR : T.1.val < lo + leftLen + rightLen := by omega
          have hinR : T ∈ tsR := (mem_rangeTests n (w' + 1) (lo + leftLen) rightLen (by omega) T).2 ⟨hge, hhiR⟩
          rw [h5T T hinR u v]
          constructor
          · intro hall y hPL hPR
            rcases hall y with hL | hR
            · rw [Fails_congr h41 (hrLp.2.2.2.1 u y), h1M u y] at hL
              exact hL ((PathOk_out_of_range n w' a T leftLen lo (by omega) (Or.inr hge) u y).1 hPL)
            · rw [Fails_congr h42 ((hrRp.2.2.2.2.2.1 T hge hhiR).1 y v), h2T T hge hhiR y v] at hR
              exact hR hPR
          · intro hall y
            by_cases hPL : PathOk n w' a none lo leftLen (by omega) u y
            · refine Or.inr ((Fails_congr h42 ((hrRp.2.2.2.2.2.1 T hge hhiR).1 y v)).2 ((h2T T hge hhiR y v).2 ?_))
              intro hPR
              exact hall y ((PathOk_out_of_range n w' a T leftLen lo (by omega) (Or.inr hge) u y).2 hPL) hPR
            · exact Or.inl ((Fails_congr h41 (hrLp.2.2.2.1 u y)).2 ((h1M u y).2 hPL))

lemma buildAll_sound (n w' : ℕ) [DecidableEq (Vis n (w' + 1))] :
    ∀ (h lo len : ℕ) (hlen : 1 ≤ len) (hhi : lo + len ≤ n) (hpow : len ≤ 2 ^ h)
      (st : St (Sum (Vis n (w' + 1)) ℕ)) (a : Vis n (w' + 1) → Bool) (aux : ℕ → Bool),
      (∀ C ∈ (buildAll n w' h lo len hlen hhi st).1.2,
        PEqualNP.ProofComplexity.ClauseSat (Sum.elim a aux) C) →
      ∀ u v, ¬ PathOk n w' a none lo len hhi u v →
        Fails (Sum.elim a aux) ((buildAll n w' h lo len hlen hhi st).2.1 u v)
  | 0, lo, len, hlen, hhi, hpow, _, a, aux, _, u, v, hno => by
    have hlen1 : len = 1 := by simp at hpow; omega
    subst hlen1
    rw [PathOk_one] at hno
    exact (leafMat_Fails_iff n w' a aux none ⟨lo, by omega⟩ u v).2 hno
  | h' + 1, lo, len, hlen, hhi, hpow, st, a, aux, hsat, u, v, hno => by
    dsimp only [buildAll] at hsat ⊢
    split_ifs with h1
    · have hlen1 : len = 1 := by omega
      subst hlen1
      rw [PathOk_one] at hno
      exact (leafMat_Fails_iff n w' a aux none ⟨lo, by omega⟩ u v).2 hno
    · simp only [h1, ↓reduceDIte] at hsat
      set leftLen := len / 2
      set rightLen := len - leftLen
      have hpow2 : 2 ^ (h' + 1) = 2 * 2 ^ h' := by ring
      have hpowL : leftLen ≤ 2 ^ h' := by omega
      have hpowR : rightLen ≤ 2 ^ h' := by omega
      set rL := buildAll n w' h' lo leftLen (by omega) (by omega) st
      set rR := buildAll n w' h' (lo + leftLen) rightLen (by omega) (by omega) rL.1
      set pM := joinMat w' rL.2.1 rR.2.1 rR.1
      set tsL := rangeTests n (w' + 1) lo leftLen (by omega)
      set tsR := rangeTests n (w' + 1) (lo + leftLen) rightLen (by omega)
      set pL := joinTestList w' rL.2.2 (fun _ => rR.2.1) tsL pM.1 (fun _ => pM.2)
      have hpL_sat : ∀ C ∈ pL.1.2, PEqualNP.ProofComplexity.ClauseSat (Sum.elim a aux) C :=
        fun C hC => hsat C (joinTestList_clauses_mono w' (fun _ => rL.2.1) rR.2.2 tsR pL.1 pL.2 C hC)
      have hpM_sat : ∀ C ∈ pM.1.2, PEqualNP.ProofComplexity.ClauseSat (Sum.elim a aux) C :=
        fun C hC => hpL_sat C (joinTestList_clauses_mono w' _ _ tsL pM.1 _ C hC)
      have hrR_sat : ∀ C ∈ rR.1.2, PEqualNP.ProofComplexity.ClauseSat (Sum.elim a aux) C :=
        fun C hC => hpM_sat C (joinPairs_clauses_mono w' _ _ _ rR.1 _ C hC)
      have hrL_sat : ∀ C ∈ rL.1.2, PEqualNP.ProofComplexity.ClauseSat (Sum.elim a aux) C := by
        have hsub : ∀ C ∈ rL.1.2, C ∈ rR.1.2 := by
          have : ∀ (h0 lo0 len0 : ℕ) (hl0 : 1 ≤ len0) (hh0 : lo0 + len0 ≤ n) (st0 : St _),
              ∀ C ∈ st0.2, C ∈ (buildAll n w' h0 lo0 len0 hl0 hh0 st0).1.2 := by
            intro h0
            induction h0 with
            | zero => intro _ _ _ _ _ _ h; exact h
            | succ h1' ih =>
              intro lo0 len0 hl0 hh0 st0 C hC
              dsimp only [buildAll]
              split_ifs
              · exact hC
              · exact joinTestList_clauses_mono w' _ _ _ _ _ C
                  (joinTestList_clauses_mono w' _ _ _ _ _ C
                    (joinPairs_clauses_mono w' _ _ _ _ _ C
                      (ih _ _ _ _ _ C (ih _ _ _ _ _ C hC))))
          exact this h' (lo + leftLen) rightLen (by omega) (by omega) rL.1
        exact fun C hC => hrR_sat C (hsub C hC)
      refine joinPairs_sound w' rL.2.1 rR.2.1 (allPairs (w' + 1)) rR.1 (fun _ _ => none)
        (Sum.elim a aux) hpM_sat u v (mem_allPairs (w' + 1) u v) ?_
      intro y
      by_cases hL : PathOk n w' a none lo leftLen (by omega) u y
      · refine Or.inr (buildAll_sound n w' h' (lo + leftLen) rightLen (by omega) (by omega) hpowR rL.1 a aux hrR_sat y v ?_)
        intro hR
        apply hno
        have hsum : leftLen + rightLen = len := by omega
        have hadd := (PathOk_add n w' a none leftLen rightLen lo (by omega) u v).2 ⟨y, hL, hR⟩
        simpa [hsum] using hadd
      · exact Or.inl (buildAll_sound n w' h' lo leftLen (by omega) (by omega) hpowL st a aux hrL_sat u y hL)

lemma buildAll_clauses_mono (n w' : ℕ) [DecidableEq (Vis n (w' + 1))] :
    ∀ (h lo len : ℕ) (hlen : 1 ≤ len) (hhi : lo + len ≤ n) (st : St (Sum (Vis n (w' + 1)) ℕ)),
      ∀ C ∈ st.2, C ∈ (buildAll n w' h lo len hlen hhi st).1.2
  | 0, _, _, _, _, _, _, hC => hC
  | h' + 1, lo, len, hlen, hhi, st, C, hC => by
    dsimp only [buildAll]
    split_ifs
    · exact hC
    · exact joinTestList_clauses_mono w' _ _ _ _ _ C
        (joinTestList_clauses_mono w' _ _ _ _ _ C
          (joinPairs_clauses_mono w' _ _ _ _ _ C
            (buildAll_clauses_mono n w' h' _ _ _ _ _ C
              (buildAll_clauses_mono n w' h' _ _ _ _ st C hC))))

lemma buildAll_up (n w' : ℕ) [DecidableEq (Vis n (w' + 1))] :
    ∀ (h lo len : ℕ) (hlen : 1 ≤ len) (hhi : lo + len ≤ n) (hpow : len ≤ 2 ^ h)
      (st : St (Sum (Vis n (w' + 1)) ℕ))
      {F : Finset (Cl (Sum (Vis n (w' + 1)) ℕ))} (ρ : Vis n (w' + 1) → Option Bool),
      (∀ C ∈ (buildAll n w' h lo len hlen hhi st).1.2, C ∈ F) →
      let res := buildAll n w' h lo len hlen hhi st
      (∀ u v, ¬ PathPoss n w' ρ none lo len hhi u v →
        KnownFail ((upStep F)^[h * (w' + 1)] (seedOf ρ)) (res.2.1 u v)) ∧
      (∀ T, lo ≤ T.1.val → T.1.val < lo + len →
        ∀ u v, ¬ PathPoss n w' ρ (some T) lo len hhi u v →
          KnownFail ((upStep F)^[h * (w' + 1)] (seedOf ρ)) (res.2.2 T u v))
  | 0, lo, len, hlen, hhi, hpow, _, F, ρ, _ => by
    have hlen1 : len = 1 := by simp at hpow; omega
    subst hlen1
    dsimp only [buildAll]
    constructor
    · intro u v hno
      rw [PathPoss_one] at hno
      simpa using (leafMat_KnownFail_iff n w' ρ none ⟨lo, by omega⟩ u v).2 hno
    · intro T _ _ u v hno
      rw [PathPoss_one] at hno
      simpa using (leafMat_KnownFail_iff n w' ρ (some T) ⟨lo, by omega⟩ u v).2 hno
  | h' + 1, lo, len, hlen, hhi, hpow, st, F, ρ, hF => by
    dsimp only [buildAll] at hF ⊢
    split_ifs with h1
    · have hlen1 : len = 1 := by omega
      subst hlen1
      have hsub : seedOf ρ ⊆ (upStep F)^[(h' + 1) * (w' + 1)] (seedOf ρ) :=
        upStep_iter_le F (seedOf ρ) (Nat.zero_le _)
      constructor
      · intro u v hno
        rw [PathPoss_one] at hno
        exact ((leafMat_KnownFail_iff n w' ρ none ⟨lo, by omega⟩ u v).2 hno).mono hsub
      · intro T _ _ u v hno
        rw [PathPoss_one] at hno
        exact ((leafMat_KnownFail_iff n w' ρ (some T) ⟨lo, by omega⟩ u v).2 hno).mono hsub
    · simp only [h1, ↓reduceDIte] at hF
      set leftLen := len / 2
      set rightLen := len - leftLen
      have hpow2 : 2 ^ (h' + 1) = 2 * 2 ^ h' := by ring
      have hpowL : leftLen ≤ 2 ^ h' := by omega
      have hpowR : rightLen ≤ 2 ^ h' := by omega
      set rL := buildAll n w' h' lo leftLen (by omega) (by omega) st
      set rR := buildAll n w' h' (lo + leftLen) rightLen (by omega) (by omega) rL.1
      set pM := joinMat w' rL.2.1 rR.2.1 rR.1
      set tsL := rangeTests n (w' + 1) lo leftLen (by omega)
      set tsR := rangeTests n (w' + 1) (lo + leftLen) rightLen (by omega)
      set pL := joinTestList w' rL.2.2 (fun _ => rR.2.1) tsL pM.1 (fun _ => pM.2)
      have hpL_F : ∀ C ∈ pL.1.2, C ∈ F :=
        fun C hC => hF C (joinTestList_clauses_mono w' (fun _ => rL.2.1) rR.2.2 tsR pL.1 pL.2 C hC)
      have hpM_F : ∀ C ∈ pM.1.2, C ∈ F :=
        fun C hC => hpL_F C (joinTestList_clauses_mono w' _ _ tsL pM.1 _ C hC)
      have hrR_F : ∀ C ∈ rR.1.2, C ∈ F :=
        fun C hC => hpM_F C (joinPairs_clauses_mono w' _ _ _ rR.1 _ C hC)
      have hrL_F : ∀ C ∈ rL.1.2, C ∈ F :=
        fun C hC => hrR_F C (buildAll_clauses_mono n w' h' _ _ _ _ rL.1 C hC)
      have ihL := buildAll_up n w' h' lo leftLen (by omega) (by omega) hpowL st ρ hrL_F
      have ihR := buildAll_up n w' h' (lo + leftLen) rightLen (by omega) (by omega) hpowR rL.1 ρ hrR_F
      have hiter : (upStep F)^[(h' + 1) * (w' + 1)] (seedOf ρ) =
          (upStep F)^[w' + 1] ((upStep F)^[h' * (w' + 1)] (seedOf ρ)) := by
        rw [← Function.iterate_add_apply]
        congr 1
        ring
      have hsum : leftLen + rightLen = len := by omega
      rw [hiter]
      constructor
      · intro u v hno
        refine joinPairs_up w' rL.2.1 rR.2.1 (allPairs (w' + 1)) rR.1 (fun _ _ => none)
          hpM_F u v (mem_allPairs (w' + 1) u v) ?_
        intro y
        by_cases hL : PathPoss n w' ρ none lo leftLen (by omega) u y
        · refine Or.inr (ihR.1 y v ?_)
          intro hR
          apply hno
          have hadd := (PathPoss_add n w' ρ none leftLen rightLen lo (by omega) u v).2 ⟨y, hL, hR⟩
          simpa [hsum] using hadd
        · exact Or.inl (ihL.1 u y hL)
      · intro T hlo hhiT u v hno
        by_cases hlt : T.1.val < lo + leftLen
        · have hnotR : T ∉ tsR := by
            intro h; have := (mem_rangeTests n (w' + 1) (lo + leftLen) rightLen (by omega) T).1 h; omega
          have hinL : T ∈ tsL := (mem_rangeTests n (w' + 1) lo leftLen (by omega) T).2 ⟨hlo, hlt⟩
          rw [joinTestList_not_mem w' (fun _ => rL.2.1) rR.2.2 tsR pL.1 pL.2 T hnotR]
          refine joinTestList_up w' rL.2.2 (fun _ => rR.2.1) tsL pM.1 (fun _ => pM.2) hpL_F T hinL u v ?_
          intro y
          by_cases hL : PathPoss n w' ρ (some T) lo leftLen (by omega) u y
          · refine Or.inr (ihR.1 y v ?_)
            intro hR
            apply hno
            have hR' := (PathPoss_out_of_range n w' ρ T rightLen (lo + leftLen) (by omega) (Or.inl hlt) y v).2 hR
            have hadd := (PathPoss_add n w' ρ (some T) leftLen rightLen lo (by omega) u v).2 ⟨y, hL, hR'⟩
            simpa [hsum] using hadd
          · exact Or.inl (ihL.2 T hlo hlt u y hL)
        · have hge : lo + leftLen ≤ T.1.val := by omega
          have hhiR : T.1.val < lo + leftLen + rightLen := by omega
          have hinR : T ∈ tsR := (mem_rangeTests n (w' + 1) (lo + leftLen) rightLen (by omega) T).2 ⟨hge, hhiR⟩
          refine joinTestList_up w' (fun _ => rL.2.1) rR.2.2 tsR pL.1 pL.2 hF T hinR u v ?_
          intro y
          by_cases hL : PathPoss n w' ρ none lo leftLen (by omega) u y
          · refine Or.inr (ihR.2 T hge hhiR y v ?_)
            intro hR
            apply hno
            have hL' := (PathPoss_out_of_range n w' ρ T leftLen lo (by omega) (Or.inr hge) u y).2 hL
            have hadd := (PathPoss_add n w' ρ (some T) leftLen rightLen lo (by omega) u v).2 ⟨y, hL', hR⟩
            simpa [hsum] using hadd
          · exact Or.inl (ihL.1 u y hL)

lemma PathOk_to_seq (n w' : ℕ) (a : Vis n (w' + 1) → Bool) (modOpt : Option (TestSpec n (w' + 1))) :
    ∀ (len lo : ℕ) (hhi : lo + len ≤ n) (u v : State (w' + 1)),
      PathOk n w' a modOpt lo len hhi u v →
      ∃ seq : ℕ → State (w' + 1), seq lo = u ∧ seq (lo + len) = v ∧
        ∀ k : ℕ, (hk1 : lo ≤ k) → (hk2 : k < lo + len) →
          StepOk n w' a modOpt ⟨k, by omega⟩ (seq k) (seq (k + 1))
  | 0, lo, _, u, v, h => by
    subst h
    exact ⟨fun _ => u, rfl, rfl, fun k hk1 hk2 => by omega⟩
  | len + 1, lo, hhi, u, v, ⟨y, hstep, hrest⟩ => by
    obtain ⟨seq, hseq0, hseq1, hsteps⟩ := PathOk_to_seq n w' a modOpt len (lo + 1) (by omega) y v hrest
    refine ⟨fun k => if k = lo then u else seq k, by simp, ?_, ?_⟩
    · have hne : lo + (len + 1) ≠ lo := by omega
      have hidx : lo + (len + 1) = lo + 1 + len := by omega
      simp only [hne, ↓reduceIte]
      rw [hidx]
      exact hseq1
    · intro k hk1 hk2
      by_cases hk : k = lo
      · subst hk
        have hne : k + 1 ≠ k := by omega
        simp only [↓reduceIte, hne, hseq0]
        exact hstep
      · have hne1 : k ≠ lo := hk
        have hne2 : k + 1 ≠ lo := by omega
        simp only [hne1, hne2, ↓reduceIte]
        exact hsteps k (by omega) (by omega)

lemma PathOk_of_seq (n w' : ℕ) (a : Vis n (w' + 1) → Bool) (modOpt : Option (TestSpec n (w' + 1))) :
    ∀ (len lo : ℕ) (hhi : lo + len ≤ n) (seq : ℕ → State (w' + 1)),
      (∀ k : ℕ, (hk1 : lo ≤ k) → (hk2 : k < lo + len) →
        StepOk n w' a modOpt ⟨k, by omega⟩ (seq k) (seq (k + 1))) →
      PathOk n w' a modOpt lo len hhi (seq lo) (seq (lo + len))
  | 0, lo, _, seq, _ => rfl
  | len + 1, lo, hhi, seq, hsteps => by
    refine ⟨seq (lo + 1), hsteps lo le_rfl (by omega), ?_⟩
    have hidx : lo + (len + 1) = lo + 1 + len := by omega
    rw [hidx]
    exact PathOk_of_seq n w' a modOpt len (lo + 1) (by omega) seq
      (fun k hk1 hk2 => hsteps k (by omega) (by omega))

lemma PathPoss_to_seq (n w' : ℕ) (ρ : Vis n (w' + 1) → Option Bool) (modOpt : Option (TestSpec n (w' + 1))) :
    ∀ (len lo : ℕ) (hhi : lo + len ≤ n) (u v : State (w' + 1)),
      PathPoss n w' ρ modOpt lo len hhi u v →
      ∃ seq : ℕ → State (w' + 1), seq lo = u ∧ seq (lo + len) = v ∧
        ∀ k : ℕ, (hk1 : lo ≤ k) → (hk2 : k < lo + len) →
          StepPoss n w' ρ modOpt ⟨k, by omega⟩ (seq k) (seq (k + 1))
  | 0, lo, _, u, v, h => by
    subst h
    exact ⟨fun _ => u, rfl, rfl, fun k hk1 hk2 => by omega⟩
  | len + 1, lo, hhi, u, v, ⟨y, hstep, hrest⟩ => by
    obtain ⟨seq, hseq0, hseq1, hsteps⟩ := PathPoss_to_seq n w' ρ modOpt len (lo + 1) (by omega) y v hrest
    refine ⟨fun k => if k = lo then u else seq k, by simp, ?_, ?_⟩
    · have hne : lo + (len + 1) ≠ lo := by omega
      have hidx : lo + (len + 1) = lo + 1 + len := by omega
      simp only [hne, ↓reduceIte]
      rw [hidx]
      exact hseq1
    · intro k hk1 hk2
      by_cases hk : k = lo
      · subst hk
        have hne : k + 1 ≠ k := by omega
        simp only [↓reduceIte, hne, hseq0]
        exact hstep
      · have hne1 : k ≠ lo := hk
        have hne2 : k + 1 ≠ lo := by omega
        simp only [hne1, hne2, ↓reduceIte]
        exact hsteps k (by omega) (by omega)

lemma PathPoss_of_seq (n w' : ℕ) (ρ : Vis n (w' + 1) → Option Bool) (modOpt : Option (TestSpec n (w' + 1))) :
    ∀ (len lo : ℕ) (hhi : lo + len ≤ n) (seq : ℕ → State (w' + 1)),
      (∀ k : ℕ, (hk1 : lo ≤ k) → (hk2 : k < lo + len) →
        StepPoss n w' ρ modOpt ⟨k, by omega⟩ (seq k) (seq (k + 1))) →
      PathPoss n w' ρ modOpt lo len hhi (seq lo) (seq (lo + len))
  | 0, lo, _, seq, _ => rfl
  | len + 1, lo, hhi, seq, hsteps => by
    refine ⟨seq (lo + 1), hsteps lo le_rfl (by omega), ?_⟩
    have hidx : lo + (len + 1) = lo + 1 + len := by omega
    rw [hidx]
    exact PathPoss_of_seq n w' ρ modOpt len (lo + 1) (by omega) seq
      (fun k hk1 hk2 => hsteps k (by omega) (by omega))

lemma cyclic_shift_eq {n w' : ℕ} (hn : 0 < n) (cy : Fin n → State (w' + 1))
    (hshift : ∀ i : Fin n, shiftCompat (cy i) (cy ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩) = true) :
    ∀ (k : ℕ) (hk : k < w' + 1) (i : Fin n),
      cy i ⟨k, hk⟩ = cy ⟨(i.val + k) % n, Nat.mod_lt _ hn⟩ ⟨0, by omega⟩
  | 0, _, i => by
    have hidx : (⟨(i.val + 0) % n, Nat.mod_lt _ hn⟩ : Fin n) = i :=
      Fin.ext (by simp [Nat.mod_eq_of_lt i.isLt])
    rw [hidx]
  | k + 1, hk, i => by
    have hsc := (shiftCompat_iff (cy i) (cy ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩)).1 (hshift i) ⟨k, by omega⟩
    rw [hsc, cyclic_shift_eq hn cy hshift k (by omega) ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩]
    congr 1
    apply Fin.ext
    simp only [Nat.mod_add_mod]
    have : i.val + 1 + k = i.val + (k + 1) := by omega
    rw [this]

lemma cyclic_edgeTuple_eq {n w' : ℕ} (hn : 0 < n) (cy : Fin n → State (w' + 1))
    (hshift : ∀ i : Fin n, shiftCompat (cy i) (cy ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩) = true)
    (i : Fin n) :
    edgeTuple (cy i) (cy ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩) =
      fun j : Fin (w' + 2) => cy ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩ ⟨0, by omega⟩ := by
  funext j
  unfold edgeTuple
  split_ifs with h0
  · have hidx : (⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩ : Fin n) = i :=
      Fin.ext (by simp [h0, Nat.mod_eq_of_lt i.isLt])
    rw [hidx]
  · rw [cyclic_shift_eq hn cy hshift (j.val - 1) (by omega) ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩]
    congr 1
    apply Fin.ext
    simp only [Nat.mod_add_mod]
    have : i.val + 1 + (j.val - 1) = i.val + j.val := by omega
    rw [this]

lemma cyclic_PathOk_to_Accepts {n w' : ℕ} (hn : 0 < n) (a : Vis n (w' + 1) → Bool)
    (s : State (w' + 1)) (hpath : PathOk n w' a none 0 n (by omega) s s) :
    Accepts n (w' + 1) hn a := by
  obtain ⟨seq, h0, hn_eq, hsteps⟩ := PathOk_to_seq n w' a none n 0 (by omega) s s hpath
  let cy : Fin n → State (w' + 1) := fun i => seq i.val
  have hnext : ∀ i : Fin n, cy ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ = seq (i.val + 1) := by
    intro i
    by_cases hlt : i.val + 1 < n
    · simp [cy, Nat.mod_eq_of_lt hlt]
    · have heq : i.val + 1 = n := by omega
      have hmod : (i.val + 1) % n = 0 := by rw [heq, Nat.mod_self]
      have hn_eq' : seq n = s := by simpa using hn_eq
      simp [cy, hmod, heq, hn_eq', h0]
  have hshift : ∀ i : Fin n, shiftCompat (cy i) (cy ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩) = true := by
    intro i
    rw [hnext i]
    exact (hsteps i.val (Nat.zero_le _) (by omega)).1
  have hbit : ∀ i : Fin n, cy i ⟨0, by omega⟩ = a (Sum.inl i) := by
    intro i
    exact (hsteps i.val (Nat.zero_le _) (by omega)).2.1.symm
  intro i
  have hstep := hsteps i.val (Nat.zero_le _) (by omega)
  have hp : a (Sum.inr (i, edgeTuple (cy i) (cy ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩))) = true := by
    rw [hnext i]
    exact hstep.2.2
  rw [cyclic_edgeTuple_eq hn cy hshift i] at hp
  have hfun : (fun j : Fin (w' + 2) => cy ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩ ⟨0, by omega⟩) =
      (fun j : Fin (w' + 2) => a (Sum.inl ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩)) := by
    funext j
    exact hbit _
  rw [hfun] at hp
  exact hp

lemma cyclic_Accepts_to_PathOk {n w' : ℕ} (hn : 0 < n) (a : Vis n (w' + 1) → Bool)
    (ha : Accepts n (w' + 1) hn a) (modOpt : Option (TestSpec n (w' + 1)))
    (hmod : ∀ T, modOpt = some T → a (testLit T).1 = !(testLit T).2) :
    ∃ s : State (w' + 1), PathOk n w' a modOpt 0 n (by omega) s s := by
  let seq : ℕ → State (w' + 1) := fun k j => a (Sum.inl ⟨(k + j.val) % n, Nat.mod_lt _ hn⟩)
  have h0n : seq 0 = seq n := by
    funext j
    simp only [seq, zero_add, Nat.add_mod_left]
  refine ⟨seq 0, ?_⟩
  have hpath := PathOk_of_seq n w' a modOpt n 0 (by omega) seq ?_
  · simpa [h0n] using hpath
  · intro k _ hk2
    have hk2' : k < n := by omega
    have hsc : shiftCompat (seq k) (seq (k + 1)) = true := by
      rw [shiftCompat_iff]
      intro j
      simp only [seq]
      have : k + (j.val + 1) = k + 1 + j.val := by omega
      rw [this]
    have hx : a (Sum.inl ⟨k, hk2'⟩) = seq k ⟨0, by omega⟩ := by
      simp [seq, Nat.mod_eq_of_lt hk2']
    have het : edgeTuple (seq k) (seq (k + 1)) =
        fun j : Fin (w' + 2) => a (Sum.inl ⟨(k + j.val) % n, Nat.mod_lt _ hn⟩) := by
      funext j
      unfold edgeTuple
      split_ifs with h0
      · simp [seq, h0]
      · simp only [seq]
        have : k + 1 + (j.val - 1) = k + j.val := by omega
        rw [this]
    have hp : a (Sum.inr (⟨k, hk2'⟩, edgeTuple (seq k) (seq (k + 1)))) = true := by
      rw [het]
      exact ha ⟨k, hk2'⟩
    refine ⟨hsc, ?_⟩
    cases modOpt with
    | none => exact ⟨hx, hp⟩
    | some T =>
      have hT := hmod T rfl
      rcases T with ⟨i', spec⟩
      cases spec with
      | inl b =>
        dsimp only
        split_ifs with hi
        · subst hi
          simp only [testLit] at hT
          exact ⟨hx.symm.trans hT, hp⟩
        · exact ⟨hx, hp⟩
      | inr t0 =>
        dsimp only
        split_ifs with hi
        · subst hi
          simp only [testLit] at hT
          refine ⟨?_, hx, hp⟩
          intro hEq
          rw [hEq] at hp
          rw [hT] at hp
          simp at hp
        · exact ⟨hx, hp⟩

lemma cyclic_PathPoss_to_Completion {n w' : ℕ} (hn : 0 < n) (ρ : Vis n (w' + 1) → Option Bool)
    (modOpt : Option (TestSpec n (w' + 1)))
    (hunset : ∀ T, modOpt = some T → ρ (testLit T).1 = none)
    (s : State (w' + 1)) (hpath : PathPoss n w' ρ modOpt 0 n (by omega) s s) :
    ∃ a : Vis n (w' + 1) → Bool, Completion n (w' + 1) hn ρ a ∧
      (∀ T, modOpt = some T → a (testLit T).1 = !(testLit T).2) := by
  classical
  obtain ⟨seq, h0, hn_eq, hsteps⟩ := PathPoss_to_seq n w' ρ modOpt n 0 (by omega) s s hpath
  let cy : Fin n → State (w' + 1) := fun i => seq i.val
  have hnext : ∀ i : Fin n, cy ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩ = seq (i.val + 1) := by
    intro i
    by_cases hlt : i.val + 1 < n
    · simp [cy, Nat.mod_eq_of_lt hlt]
    · have heq : i.val + 1 = n := by omega
      have hmod : (i.val + 1) % n = 0 := by rw [heq, Nat.mod_self]
      have hn_eq' : seq n = s := by simpa using hn_eq
      simp [cy, hmod, heq, hn_eq', h0]
  have hshift : ∀ i : Fin n, shiftCompat (cy i) (cy ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩) = true := by
    intro i
    rw [hnext i]
    exact (hsteps i.val (Nat.zero_le _) (by omega)).1
  let a : Vis n (w' + 1) → Bool := fun v =>
    match v with
    | Sum.inl i => cy i ⟨0, by omega⟩
    | Sum.inr p =>
      match ρ (Sum.inr p) with
      | some b => b
      | none =>
        match modOpt with
        | some (i0, Sum.inr t0) => if p = (i0, t0) then false else true
        | _ => true
  refine ⟨a, ⟨?_, ?_⟩, ?_⟩
  · intro i
    have hstep := hsteps i.val (Nat.zero_le _) (by omega)
    have hstep_p : ρ (Sum.inr (i, edgeTuple (cy i) (cy ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩))) ≠ some false := by
      rw [hnext i]
      have h2 := hstep.2
      cases modOpt with
      | none => exact h2.2
      | some T =>
        rcases T with ⟨i', spec⟩
        cases spec with
        | inl b => dsimp only at h2; split_ifs at h2 <;> exact h2.2
        | inr t0 => dsimp only at h2; split_ifs at h2; exact h2.2.2; exact h2.2
    have het : (fun j : Fin (w' + 2) => a (Sum.inl ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩)) =
        edgeTuple (cy i) (cy ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩) :=
      (cyclic_edgeTuple_eq hn cy hshift i).symm
    rw [het]
    dsimp only [a]
    cases hrv : ρ (Sum.inr (i, edgeTuple (cy i) (cy ⟨(i.val + 1) % n, Nat.mod_lt _ hn⟩))) with
    | some b =>
      cases b
      · exact absurd hrv hstep_p
      · rfl
    | none =>
      cases hmod : modOpt with
      | none => rfl
      | some T =>
        rcases T with ⟨i0, spec⟩
        cases spec with
        | inl b0 => rfl
        | inr t0 =>
          dsimp only
          split_ifs with heq
          · rcases Prod.mk.inj heq with ⟨rfl, htEq⟩
            rw [hmod] at hstep
            have h2 := hstep.2
            simp only [↓reduceIte] at h2
            rw [← hnext i] at h2
            exact absurd htEq h2.1
          · rfl
  · intro v b hrv
    cases v with
    | inl i =>
      change cy i ⟨0, by omega⟩ = b
      have hstep := hsteps i.val (Nat.zero_le _) (by omega)
      have h2 := hstep.2
      by_contra hne
      have hnb : b = !(cy i ⟨0, by omega⟩) := bool_eq_not_of_ne hne
      rw [hnb] at hrv
      cases hmod : modOpt with
      | none =>
        rw [hmod] at h2
        exact h2.1 hrv
      | some T =>
        rcases T with ⟨i', spec⟩
        cases spec with
        | inl b' =>
          by_cases hi : i' = i
          · subst hi
            have := hunset (i', Sum.inl b') hmod
            simp only [testLit] at this
            rw [this] at hrv
            simp at hrv
          · rw [hmod] at h2
            simp only [hi, ↓reduceIte] at h2
            exact h2.1 hrv
        | inr t0 =>
          rw [hmod] at h2
          dsimp only at h2
          split_ifs at h2
          · exact h2.2.1 hrv
          · exact h2.1 hrv
    | inr p =>
      dsimp only [a]
      rw [hrv]
  · intro T hmod
    have hnone := hunset T hmod
    rcases T with ⟨i0, spec⟩
    cases spec with
    | inl b0 =>
      simp only [testLit] at hnone ⊢
      have hstep := hsteps i0.val (Nat.zero_le _) (by omega)
      rw [hmod] at hstep
      have h2 := hstep.2
      simp only [↓reduceIte] at h2
      exact h2.1
    | inr t0 =>
      simp only [testLit] at hnone ⊢
      dsimp only [a]
      rw [hnone, hmod]
      simp

lemma cyclic_Completion_to_PathPoss {n w' : ℕ} (hn : 0 < n) (ρ : Vis n (w' + 1) → Option Bool)
    (a : Vis n (w' + 1) → Bool) (hcomp : Completion n (w' + 1) hn ρ a)
    (modOpt : Option (TestSpec n (w' + 1)))
    (hmod : ∀ T, modOpt = some T → a (testLit T).1 = !(testLit T).2) :
    ∃ s : State (w' + 1), PathPoss n w' ρ modOpt 0 n (by omega) s s := by
  obtain ⟨s, hpath⟩ := cyclic_Accepts_to_PathOk hn a hcomp.1 modOpt hmod
  obtain ⟨seq, h0, hn_eq, hsteps⟩ := PathOk_to_seq n w' a modOpt n 0 (by omega) s s hpath
  refine ⟨s, ?_⟩
  have hpp : PathPoss n w' ρ modOpt 0 n (by omega) (seq 0) (seq (0 + n)) := by
    apply PathPoss_of_seq n w' ρ modOpt n 0 (by omega) seq
    intro k _ hk2
    have hs := hsteps k (Nat.zero_le _) hk2
    refine ⟨hs.1, ?_⟩
    have hnot_x : ∀ (i : Fin n) (b : Bool), a (Sum.inl i) = b → ρ (Sum.inl i) ≠ some (!b) := by
      intro i b hax hrv
      have := hcomp.2 (Sum.inl i) (!b) hrv
      rw [hax] at this
      cases b <;> simp at this
    have hnot_p : ∀ (i : Fin n) (t : Fin (w' + 2) → Bool), a (Sum.inr (i, t)) = true →
        ρ (Sum.inr (i, t)) ≠ some false := by
      intro i t hap hrv
      have := hcomp.2 (Sum.inr (i, t)) false hrv
      rw [hap] at this
      simp at this
    cases modOpt with
    | none =>
      exact ⟨hnot_x _ _ hs.2.1, hnot_p _ _ hs.2.2⟩
    | some T =>
      rcases T with ⟨i', spec⟩
      cases spec with
      | inl b =>
        have h2 := hs.2
        dsimp only at h2 ⊢
        split_ifs at h2 ⊢
        · exact ⟨h2.1, hnot_p _ _ h2.2⟩
        · exact ⟨hnot_x _ _ h2.1, hnot_p _ _ h2.2⟩
      | inr t0 =>
        have h2 := hs.2
        dsimp only at h2 ⊢
        split_ifs at h2 ⊢
        · exact ⟨h2.1, hnot_x _ _ h2.2.1, hnot_p _ _ h2.2.2⟩
        · exact ⟨hnot_x _ _ h2.1, hnot_p _ _ h2.2⟩
  have hn_eq' : seq n = s := by simpa using hn_eq
  have hpp' : PathPoss n w' ρ modOpt 0 n (by omega) (seq 0) (seq n) := by simpa using hpp
  rwa [h0, hn_eq'] at hpp'

def foldDiagTests {n : ℕ} (w' : ℕ) [DecidableEq (Vis n (w' + 1))]
    (mods : TestSpec n (w' + 1) → MatRep (w' + 1) (Sum (Vis n (w' + 1)) ℕ)) :
    List (TestSpec n (w' + 1)) → St (Sum (Vis n (w' + 1)) ℕ) → St (Sum (Vis n (w' + 1)) ℕ)
  | [], st => st
  | T :: rest, st =>
    let st1 := foldDiag w' (fun s => mods T s s) (some (Sum.inl (testLit T).1, (testLit T).2)) st
    foldDiagTests w' mods rest st1

lemma foldDiagTests_clauses_mono {n : ℕ} (w' : ℕ) [DecidableEq (Vis n (w' + 1))]
    (mods : TestSpec n (w' + 1) → MatRep (w' + 1) (Sum (Vis n (w' + 1)) ℕ)) :
    ∀ (ts : List (TestSpec n (w' + 1))) (st : St (Sum (Vis n (w' + 1)) ℕ)),
      ∀ C ∈ st.2, C ∈ (foldDiagTests w' mods ts st).2
  | [], _, _, hC => hC
  | T :: rest, st, C, hC => by
    dsimp only [foldDiagTests, foldDiag]
    exact foldDiagTests_clauses_mono w' mods rest _ C
      (List.mem_append_right _ (foldBool_clauses_mono w' _ _ C (foldBool_clauses_mono w' _ st C hC)))

lemma foldDiagTests_props {n : ℕ} (w' : ℕ) [DecidableEq (Vis n (w' + 1))]
    (mods : TestSpec n (w' + 1) → MatRep (w' + 1) (Sum (Vis n (w' + 1)) ℕ)) :
    ∀ (ts : List (TestSpec n (w' + 1))) (st : St (Sum (Vis n (w' + 1)) ℕ)),
      ValidSt st →
      (∀ T ∈ ts, ValidMat st.1 (mods T) ∧ ∀ u v, rLen (mods T u v) ≤ 2) →
      let st' := foldDiagTests w' mods ts st
      ValidSt st' ∧ st.1 ≤ st'.1 ∧ (∀ C ∈ st.2, C ∈ st'.2) ∧
      stCost st' ≤ stCost st + ts.length * unitCost w'
  | [], st, hst, _ => by
    dsimp only [foldDiagTests]
    exact ⟨hst, le_rfl, fun _ h => h, by simp⟩
  | T0 :: rest, st, hst, hts => by
    dsimp only [foldDiagTests]
    have hT0 := hts T0 (List.mem_cons_self ..)
    set st1 := foldDiag w' (fun s => mods T0 s s) (some (Sum.inl (testLit T0).1, (testLit T0).2)) st
    have hp1 := foldDiag_props w' (fun s => mods T0 s s)
      (some (Sum.inl (testLit T0).1, (testLit T0).2)) st hst
      (fun s => hT0.1 s s) (fun s => hT0.2 s s)
      (fun l hl => by have := Option.some.inj hl; subst this; intro k hk; simp at hk)
    have hp2 := foldDiagTests_props w' mods rest st1 hp1.1
      (fun T hT => let h := hts T (List.mem_cons_of_mem T0 hT); ⟨h.1.mono hp1.2.1, h.2⟩)
    refine ⟨hp2.1, hp1.2.1.trans hp2.2.1, fun C hC => hp2.2.2.1 C (hp1.2.2.1 C hC), ?_⟩
    have h1 : stCost st1 ≤ stCost st + unitCost w' := hp1.2.2.2
    have h2 : stCost (foldDiagTests w' mods rest st1) ≤ stCost st1 + rest.length * unitCost w' := hp2.2.2.2
    simp only [List.length_cons]
    have : (rest.length + 1) * unitCost w' = rest.length * unitCost w' + unitCost w' := by ring
    omega

lemma foldDiagTests_ext {n : ℕ} (w' : ℕ) [DecidableEq (Vis n (w' + 1))]
    (mods : TestSpec n (w' + 1) → MatRep (w' + 1) (Sum (Vis n (w' + 1)) ℕ)) :
    ∀ (ts : List (TestSpec n (w' + 1))) (st : St (Sum (Vis n (w' + 1)) ℕ)),
      ValidSt st →
      (∀ T ∈ ts, ValidMat st.1 (mods T) ∧ ∀ u v, rLen (mods T u v) ≤ 2) →
      ∀ (a : Vis n (w' + 1) → Bool) (aux0 : ℕ → Bool),
        (∀ C ∈ st.2, PEqualNP.ProofComplexity.ClauseSat (Sum.elim a aux0) C) →
        (∀ T ∈ ts, (∀ s, Fails (Sum.elim a aux0) (mods T s s)) → a (testLit T).1 = (testLit T).2) →
        ∃ aux1 : ℕ → Bool,
          (∀ k < st.1, aux1 k = aux0 k) ∧
          (∀ C ∈ (foldDiagTests w' mods ts st).2, PEqualNP.ProofComplexity.ClauseSat (Sum.elim a aux1) C)
  | [], _, _, _, _, aux0, hsat, _ => ⟨aux0, fun _ _ => rfl, hsat⟩
  | T0 :: rest, st, hst, hts, a, aux0, hsat, himp => by
    dsimp only [foldDiagTests]
    have hT0 := hts T0 (List.mem_cons_self ..)
    set st1 := foldDiag w' (fun s => mods T0 s s) (some (Sum.inl (testLit T0).1, (testLit T0).2)) st
    have hp1 := foldDiag_props w' (fun s => mods T0 s s)
      (some (Sum.inl (testLit T0).1, (testLit T0).2)) st hst
      (fun s => hT0.1 s s) (fun s => hT0.2 s s)
      (fun l hl => by have := Option.some.inj hl; subst this; intro k hk; simp at hk)
    obtain ⟨aux1, h1ag, h1sat⟩ :=
      foldDiag_ext_some w' (fun s => mods T0 s s) (Sum.inl (testLit T0).1, (testLit T0).2) st hst
        (fun s => hT0.1 s s) (fun k hk => by simp at hk) a aux0 hsat (himp T0 (List.mem_cons_self ..))
    obtain ⟨aux2, h2ag, h2sat⟩ :=
      foldDiagTests_ext w' mods rest st1 hp1.1
        (fun T hT => let h := hts T (List.mem_cons_of_mem T0 hT); ⟨h.1.mono hp1.2.1, h.2⟩)
        a aux1 h1sat
        (fun T hT hF => himp T (List.mem_cons_of_mem T0 hT)
          (fun s => (Fails_congr h1ag ((hts T (List.mem_cons_of_mem T0 hT)).1 s s)).1 (hF s)))
    exact ⟨aux2, fun k hk => (h2ag k (Nat.lt_of_lt_of_le hk hp1.2.1)).trans (h1ag k hk), h2sat⟩

lemma foldDiagTests_up {n : ℕ} (w' : ℕ) [DecidableEq (Vis n (w' + 1))]
    (mods : TestSpec n (w' + 1) → MatRep (w' + 1) (Sum (Vis n (w' + 1)) ℕ)) :
    ∀ (ts : List (TestSpec n (w' + 1))) (st : St (Sum (Vis n (w' + 1)) ℕ))
      {F : Finset (Cl (Sum (Vis n (w' + 1)) ℕ))} {K : Set (Lit (Sum (Vis n (w' + 1)) ℕ))},
      (∀ C ∈ (foldDiagTests w' mods ts st).2, C ∈ F) →
      ∀ T ∈ ts, (∀ s, KnownFail K (mods T s s)) →
        (Sum.inl (testLit T).1, (testLit T).2) ∈ (upStep F)^[w' + 1] K
  | [], _, _, _, _, _, h, _ => by simp at h
  | T0 :: rest, st, F, K, hF, T, hT, hall => by
    dsimp only [foldDiagTests] at hF
    set st1 := foldDiag w' (fun s => mods T0 s s) (some (Sum.inl (testLit T0).1, (testLit T0).2)) st
    rcases List.mem_cons.1 hT with rfl | hmem
    · have hF1 : ∀ C ∈ st1.2, C ∈ F := fun C hC => hF C (foldDiagTests_clauses_mono w' mods rest st1 C hC)
      exact foldDiag_up_some w' (fun s => mods T s s) (Sum.inl (testLit T).1, (testLit T).2) st hF1 hall
    · exact foldDiagTests_up w' mods rest st1 hF T hmem hall

def mapVar {V : Type} (m : ℕ) (hm : 0 < m) : Sum V ℕ → Sum V (Fin m)
  | Sum.inl v => Sum.inl v
  | Sum.inr k => Sum.inr (if h : k < m then ⟨k, h⟩ else ⟨0, hm⟩)

def mapLit {V : Type} (m : ℕ) (hm : 0 < m) (l : Lit (Sum V ℕ)) : Lit (Sum V (Fin m)) :=
  (mapVar m hm l.1, l.2)

def mapCl {V : Type} [DecidableEq V] (m : ℕ) (hm : 0 < m) (C : Cl (Sum V ℕ)) : Cl (Sum V (Fin m)) :=
  C.image (mapLit m hm)

lemma mapLit_negL {V : Type} (m : ℕ) (hm : 0 < m) (l : Lit (Sum V ℕ)) :
    mapLit m hm (negL l) = negL (mapLit m hm l) := rfl

lemma mapCl_card_le {V : Type} [DecidableEq V] (m : ℕ) (hm : 0 < m) (C : Cl (Sum V ℕ)) :
    (mapCl m hm C).card ≤ C.card := Finset.card_image_le

lemma mapCl_sat_of_nat {V : Type} [DecidableEq V] (m : ℕ) (hm : 0 < m) (a : V → Bool)
    (aux : ℕ → Bool) {C : Cl (Sum V ℕ)} (hV : ValidCl m C)
    (hsat : PEqualNP.ProofComplexity.ClauseSat (Sum.elim a aux) C) :
    PEqualNP.ProofComplexity.ClauseSat (Sum.elim a (fun k : Fin m => aux k.val)) (mapCl m hm C) := by
  obtain ⟨l, hlC, hl⟩ := hsat
  refine ⟨mapLit m hm l, Finset.mem_image.2 ⟨l, hlC, rfl⟩, ?_⟩
  cases hx : l.1 with
  | inl v => simpa [mapLit, mapVar, hx] using hl
  | inr k =>
    have hk : k < m := hV l hlC k hx
    simpa [mapLit, mapVar, hx, hk] using hl

lemma mapCl_sat_to_nat {V : Type} [DecidableEq V] (m : ℕ) (hm : 0 < m) (a : V → Bool)
    (aux : Fin m → Bool) {C : Cl (Sum V ℕ)} (hV : ValidCl m C)
    (hsat : PEqualNP.ProofComplexity.ClauseSat (Sum.elim a aux) (mapCl m hm C)) :
    PEqualNP.ProofComplexity.ClauseSat (Sum.elim a (fun k => if h : k < m then aux ⟨k, h⟩ else false)) C := by
  obtain ⟨l', hl'C, hl'⟩ := hsat
  rcases Finset.mem_image.1 hl'C with ⟨l, hlC, rfl⟩
  refine ⟨l, hlC, ?_⟩
  cases hx : l.1 with
  | inl v => simpa [mapLit, mapVar, hx] using hl'
  | inr k =>
    have hk : k < m := hV l hlC k hx
    simpa [mapLit, mapVar, hx, hk] using hl'

lemma upStep_map_transport {V : Type} [DecidableEq V] (m : ℕ) (hm : 0 < m)
    (Fnat : Finset (Cl (Sum V ℕ))) (Ffin : Finset (Cl (Sum V (Fin m))))
    (hV : ∀ C ∈ Fnat, ValidCl m C)
    (himg : ∀ C ∈ Fnat, mapCl m hm C ∈ Ffin)
    (ρ : V → Option Bool) :
    ∀ k : ℕ, ∀ l ∈ (upStep Fnat)^[k] (seedOf ρ),
      mapLit m hm l ∈ (upStep Ffin)^[k] (seedOf ρ)
  | 0, l, hl => by
    rcases hl with ⟨v, hv, hrv⟩
    refine ⟨v, ?_, hrv⟩
    simp [mapLit, mapVar, hv]
  | k + 1, l, hl => by
    rw [Function.iterate_succ_apply'] at hl ⊢
    rcases hl with hl | ⟨D, hD, hlD, hother⟩
    · exact Or.inl (upStep_map_transport m hm Fnat Ffin hV himg ρ k l hl)
    · refine Or.inr ⟨mapCl m hm D, himg D hD, Finset.mem_image.2 ⟨l, hlD, rfl⟩, ?_⟩
      intro o' ho' hne'
      rcases Finset.mem_image.1 ho' with ⟨o, hoD, rfl⟩
      have hne : o ≠ l := fun h => hne' (by rw [h])
      have hprev := hother o hoD hne
      rw [← mapLit_negL m hm o]
      exact upStep_map_transport m hm Fnat Ffin hV himg ρ k (negL o) hprev

lemma upper_bound_wsucc (n w' : ℕ) (hn : 0 < n) :
    let w := w' + 1
    let height := Nat.clog 2 n
    let rounds := w * (height + 1)
    ∃ (m : ℕ) (F : Finset (Cl (Sum (Vis n w) (Fin m)))),
      (∀ D ∈ F, D.card ≤ 3) ∧
      (∀ total : Vis n w → Bool, Accepts n w hn total ↔ ∃ aux : Fin m → Bool,
        PEqualNP.ProofComplexity.Satisfies (Sum.elim total aux) (↑F : Set (Cl (Sum (Vis n w) (Fin m))))) ∧
      (∀ ρ : Vis n w → Option Bool,
        ((¬ ∃ a : Vis n w → Bool, Completion n w hn ρ a) ↔
          ∃ D ∈ F, ∀ l ∈ D, negL l ∈ (upStep F)^[rounds] (seedOf ρ)) ∧
        ((∃ a : Vis n w → Bool, Completion n w hn ρ a) → ∀ v : Vis n w, ∀ b : Bool,
          (∀ a : Vis n w → Bool, Completion n w hn ρ a → a v = b) ↔
          (Sum.inl v, b) ∈ (upStep F)^[rounds] (seedOf ρ))) ∧
      m + (∑ D ∈ F, D.card) ≤ 256 * (n + 1) * (height + 1) * 16 ^ w := by
  classical
  let w := w' + 1
  let h := Nat.clog 2 n
  have hn_pow : n ≤ 2 ^ h := (Nat.clog_le_iff_le_pow (by omega)).1 le_rfl
  let res := buildAll n w' h 0 n hn (by omega) (0, [])
  let st1 := foldDiag w' (fun s => res.2.1 s s) none res.1
  let tsAll := rangeTests n w 0 n (by omega)
  let st2 := foldDiagTests w' res.2.2 tsAll st1
  have hst0 : ValidSt (V := Vis n w) (0, []) := fun _ hC => by simp at hC
  have hresP := buildAll_props n w' h 0 n hn (by omega) (0, []) hst0
  have hst1P := foldDiag_props w' (fun s => res.2.1 s s) none res.1 hresP.1
    (fun s => hresP.2.2.2.1 s s) (fun s => hresP.2.2.2.2.1 s s) (fun _ h => by simp at h)
  have htsAllP : ∀ T ∈ tsAll, ValidMat st1.1 (res.2.2 T) ∧ ∀ u v, rLen (res.2.2 T u v) ≤ 2 := by
    intro T _
    have h1 := hresP.2.2.2.2.2.1 T (Nat.zero_le _) (by omega)
    exact ⟨h1.1.mono hst1P.2.1, h1.2⟩
  have hst2P := foldDiagTests_props w' res.2.2 tsAll st1 hst1P.1 htsAllP
  let m : ℕ := st2.1 + 1
  have hm : 0 < m := by omega
  have hst2_le_m : st2.1 ≤ m := by omega
  let Fnat : Finset (Cl (Sum (Vis n w) ℕ)) := st2.2.toFinset
  let Lfin : List (Cl (Sum (Vis n w) (Fin m))) := st2.2.map (mapCl m hm)
  let Ffin : Finset (Cl (Sum (Vis n w) (Fin m))) := Lfin.toFinset
  have hValidFnat : ∀ C ∈ Fnat, ValidCl m C := by
    intro C hC
    exact (hst2P.1 C (List.mem_toFinset.1 hC)).2.mono hst2_le_m
  have hImgF : ∀ C ∈ Fnat, mapCl m hm C ∈ Ffin := fun C hC =>
    List.mem_toFinset.2 (List.mem_map.2 ⟨C, List.mem_toFinset.1 hC, rfl⟩)
  have hcard3 : ∀ D ∈ Ffin, D.card ≤ 3 := by
    intro D hD
    rcases List.mem_map.1 (List.mem_toFinset.1 hD) with ⟨C, hC, rfl⟩
    exact (mapCl_card_le m hm C).trans (hst2P.1 C hC).1
  have hsat : ∀ total : Vis n w → Bool, Accepts n w hn total ↔ ∃ aux : Fin m → Bool,
      PEqualNP.ProofComplexity.Satisfies (Sum.elim total aux) (↑Ffin : Set (Cl (Sum (Vis n w) (Fin m)))) := by
    intro total
    constructor
    · intro hacc
      obtain ⟨aux1, _, h1sat, h1M, h1T⟩ :=
        buildAll_ext n w' h 0 n hn (by omega) hn_pow (0, []) hst0 total (fun _ => false)
          (fun _ hC => by simp at hC)
      have hexMain : ∃ s, ¬ Fails (Sum.elim total aux1) (res.2.1 s s) := by
        obtain ⟨s, hpath⟩ := cyclic_Accepts_to_PathOk hn total hacc none (fun _ h => by simp at h)
        exact ⟨s, fun hF => (h1M s s).1 hF hpath⟩
      obtain ⟨aux2, h2ag, h2sat⟩ :=
        foldDiag_ext_none w' (fun s => res.2.1 s s) res.1 hresP.1 (fun s => hresP.2.2.2.1 s s)
          total aux1 h1sat hexMain
      have himpT : ∀ T ∈ tsAll, (∀ s, Fails (Sum.elim total aux2) (res.2.2 T s s)) →
          total (testLit T).1 = (testLit T).2 := by
        intro T _ hF
        by_contra hne
        have hopp : total (testLit T).1 = !(testLit T).2 := by
          cases h1 : total (testLit T).1 <;> cases h2 : (testLit T).2 <;> simp_all
        obtain ⟨s, hpath⟩ := cyclic_Accepts_to_PathOk hn total hacc (some T) (fun T' hEq => by
          have := Option.some.inj hEq; subst this; exact hopp)
        have hF1 : Fails (Sum.elim total aux1) (res.2.2 T s s) :=
          (Fails_congr h2ag ((hresP.2.2.2.2.2.1 T (Nat.zero_le _) (by omega)).1 s s)).1 (hF s)
        exact (h1T T (Nat.zero_le _) (by omega) s s).1 hF1 hpath
      obtain ⟨aux3, _, h3sat⟩ :=
        foldDiagTests_ext w' res.2.2 tsAll st1 hst1P.1 htsAllP total aux2 h2sat himpT
      refine ⟨fun k : Fin m => aux3 k.val, ?_⟩
      intro D hD
      rcases List.mem_map.1 (List.mem_toFinset.1 hD) with ⟨C, hC, rfl⟩
      exact mapCl_sat_of_nat m hm total aux3 ((hst2P.1 C hC).2.mono hst2_le_m) (h3sat C hC)
    · rintro ⟨auxFin, haux⟩
      let auxNat : ℕ → Bool := fun k => if hk : k < m then auxFin ⟨k, hk⟩ else false
      have hnatSat : ∀ C ∈ st2.2, PEqualNP.ProofComplexity.ClauseSat (Sum.elim total auxNat) C := by
        intro C hC
        have hD : mapCl m hm C ∈ Ffin := List.mem_toFinset.2 (List.mem_map.2 ⟨C, hC, rfl⟩)
        exact mapCl_sat_to_nat m hm total auxFin ((hst2P.1 C hC).2.mono hst2_le_m) (haux _ hD)
      have hst1Sat : ∀ C ∈ st1.2, PEqualNP.ProofComplexity.ClauseSat (Sum.elim total auxNat) C :=
        fun C hC => hnatSat C (foldDiagTests_clauses_mono w' res.2.2 tsAll st1 C hC)
      have hresSat : ∀ C ∈ res.1.2, PEqualNP.ProofComplexity.ClauseSat (Sum.elim total auxNat) C :=
        fun C hC => hst1Sat C (hst1P.2.2.1 C hC)
      obtain ⟨s, hs⟩ := foldDiag_sound_none w' (fun s => res.2.1 s s) res.1 (Sum.elim total auxNat) hst1Sat
      have hpath : PathOk n w' total none 0 n (by omega) s s := by
        by_contra hno
        exact hs (buildAll_sound n w' h 0 n hn (by omega) hn_pow (0, []) total auxNat hresSat s s hno)
      exact cyclic_PathOk_to_Accepts hn total s hpath
  refine ⟨m, Ffin, hcard3, hsat, ?_, ?_⟩
  · intro ρ
    have hresF : ∀ C ∈ res.1.2, C ∈ Fnat := fun C hC =>
      List.mem_toFinset.2 (hst2P.2.2.1 C (hst1P.2.2.1 C hC))
    have hst1F : ∀ C ∈ st1.2, C ∈ Fnat := fun C hC =>
      List.mem_toFinset.2 (hst2P.2.2.1 C hC)
    have hst2F : ∀ C ∈ st2.2, C ∈ Fnat := fun C hC => List.mem_toFinset.2 hC
    have hupAll := buildAll_up n w' h 0 n hn (by omega) hn_pow (0, []) (F := Fnat) ρ hresF
    have hiterR : w * (h + 1) = (w' + 1) + h * (w' + 1) := by dsimp only [w]; ring
    constructor
    · constructor
      · intro hno
        have hnoPath : ∀ s : State w, ¬ PathPoss n w' ρ none 0 n (by omega) s s := by
          intro s hpath
          obtain ⟨a, hcomp, _⟩ := cyclic_PathPoss_to_Completion hn ρ none (fun _ h => by simp at h) s hpath
          exact hno ⟨a, hcomp⟩
        have hKF : ∀ s : State w, KnownFail ((upStep Fnat)^[h * (w' + 1)] (seedOf ρ)) (res.2.1 s s) :=
          fun s => hupAll.1 s s (hnoPath s)
        obtain ⟨D, hDF, hDfalse⟩ := foldDiag_up_none w' (fun s => res.2.1 s s) res.1 hst1F hKF
        refine ⟨mapCl m hm D, hImgF D hDF, ?_⟩
        intro l' hl'
        rcases Finset.mem_image.1 hl' with ⟨l, hlD, rfl⟩
        have hmem1 : negL l ∈ (upStep Fnat)^[w' + h * (w' + 1)] (seedOf ρ) := by
          rw [Function.iterate_add_apply]
          exact hDfalse l hlD
        have hmem2 : negL l ∈ (upStep Fnat)^[w * (h + 1)] (seedOf ρ) :=
          upStep_iter_le Fnat (seedOf ρ) (by omega) hmem1
        rw [← mapLit_negL m hm l]
        exact upStep_map_transport m hm Fnat Ffin hValidFnat hImgF ρ (w * (h + 1)) (negL l) hmem2
      · intro hconf hcomp
        exact enc_conflict_sound (fun t ht => (hsat t).1 ht) hcomp hconf
    · intro hcomp v b
      constructor
      · intro hforced
        cases hrv : ρ v with
        | some b' =>
          obtain ⟨a, ha⟩ := hcomp
          have hb1 : a v = b' := ha.2 v b' hrv
          have hb2 : a v = b := hforced a ha
          have hbe : b' = b := hb1.symm.trans hb2
          subst hbe
          exact upStep_iter_le Ffin (seedOf ρ) (Nat.zero_le _) ⟨v, rfl, hrv⟩
        | none =>
          have hT : ∃ T : TestSpec n w, testLit T = (v, b) := by
            cases v with
            | inl i => exact ⟨(i, Sum.inl b), rfl⟩
            | inr p =>
              rcases p with ⟨i, t⟩
              have hbT : b = true := by
                obtain ⟨a, ha, hρa⟩ := hcomp
                let a' : Vis n w → Bool := fun u => if u = Sum.inr (i, t) then true else a u
                have hcomp' : Completion n w hn ρ a' := by
                  refine ⟨?_, ?_⟩
                  · intro j
                    have hinl : ∀ u : Fin n, a' (Sum.inl u) = a (Sum.inl u) := fun _ => by simp [a']
                    have hfn : (fun k : Fin (w + 1) => a' (Sum.inl ⟨(j.val + k.val) % n, Nat.mod_lt _ hn⟩)) =
                        (fun k : Fin (w + 1) => a (Sum.inl ⟨(j.val + k.val) % n, Nat.mod_lt _ hn⟩)) := by
                      funext k; exact hinl _
                    rw [hfn]
                    dsimp only [a']
                    split_ifs
                    · rfl
                    · exact ha j
                  · intro u c hru
                    by_cases heq : u = Sum.inr (i, t)
                    · subst heq; rw [hrv] at hru; simp at hru
                    · simp [a', heq, hρa u c hru]
                have := hforced a' hcomp'
                simpa [a'] using this.symm
              subst hbT
              exact ⟨(i, Sum.inr t), rfl⟩
          obtain ⟨T, hTlit⟩ := hT
          have hTin : T ∈ tsAll := (mem_rangeTests n w 0 n (by omega) T).2 ⟨Nat.zero_le _, by simpa using T.1.isLt⟩
          have hnoPath : ∀ s : State w, ¬ PathPoss n w' ρ (some T) 0 n (by omega) s s := by
            intro s hpath
            obtain ⟨a, hcomp', hopp⟩ := cyclic_PathPoss_to_Completion hn ρ (some T)
              (fun T' hEq => by
                have := Option.some.inj hEq; subst this
                rw [hTlit]; exact hrv) s hpath
            have h1 := hopp T rfl
            rw [hTlit] at h1
            have h2 := hforced a hcomp'
            rw [h2] at h1
            cases b <;> simp at h1
          have hKF : ∀ s : State w, KnownFail ((upStep Fnat)^[h * (w' + 1)] (seedOf ρ)) (res.2.2 T s s) :=
            fun s => hupAll.2 T (Nat.zero_le _) (by omega) s s (hnoPath s)
          have hmemNat : (Sum.inl (testLit T).1, (testLit T).2) ∈
              (upStep Fnat)^[w' + 1] ((upStep Fnat)^[h * (w' + 1)] (seedOf ρ)) :=
            foldDiagTests_up w' res.2.2 tsAll st1 hst2F T hTin hKF
          rw [← Function.iterate_add_apply, ← hiterR, hTlit] at hmemNat
          have htr := upStep_map_transport m hm Fnat Ffin hValidFnat hImgF ρ (w * (h + 1)) (Sum.inl v, b) hmemNat
          simpa [mapLit, mapVar] using htr
      · exact enc_force_sound (fun t ht => (hsat t).1 ht)
  · have hsum1 : (∑ D ∈ Ffin, D.card) ≤ (Lfin.map Finset.card).sum := by
      show (∑ D ∈ Lfin.toFinset, D.card) ≤ (Lfin.map Finset.card).sum
      exact sum_toFinset_card_le Lfin
    have hsum2 : (Lfin.map Finset.card).sum ≤ 3 * Lfin.length := by
      refine sum_map_card_le Lfin 3 ?_
      intro D hD
      exact hcard3 D (List.mem_toFinset.2 hD)
    have hLlen : Lfin.length = st2.2.length := by simp [Lfin]
    have hcost0 : stCost (W := Sum (Vis n w) ℕ) (0, []) = 0 := rfl
    have htslen : tsAll.length = n * (2 + 2 ^ (w' + 2)) := rangeTests_length n w 0 n (by omega)
    have hcost_total : stCost st2 ≤ (n + (h + 1) * n * (2 + 2 ^ (w' + 2))) * unitCost w' := by
      have hc1 : stCost res.1 ≤ stCost (0, []) + (n - 1 + h * n * (2 + 2 ^ (w' + 2))) * unitCost w' :=
        hresP.2.2.2.2.2.2
      have hc2 : stCost st1 ≤ stCost res.1 + unitCost w' := hst1P.2.2.2
      have hc3 : stCost st2 ≤ stCost st1 + tsAll.length * unitCost w' := hst2P.2.2.2
      rw [hcost0, zero_add] at hc1
      rw [htslen] at hc3
      set K := 2 + 2 ^ (w' + 2)
      have hcoeff : ((n - 1) + h * n * K) + 1 + n * K = n + (h + 1) * n * K := by
        have hsub : (n - 1) + 1 = n := by omega
        have hmul : h * n * K + n * K = (h + 1) * n * K := by ring
        omega
      have hsum : stCost st2 ≤ (((n - 1) + h * n * K) + 1 + n * K) * unitCost w' := by nlinarith
      rwa [hcoeff] at hsum
    have hpow2 : 2 ≤ 2 ^ w := by
      have : 2 ^ 1 ≤ 2 ^ (w' + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      simpa [w] using this
    have hK_le : 2 + 2 ^ (w' + 2) ≤ 3 * 2 ^ w := by
      have : 2 ^ (w' + 2) = 2 * 2 ^ w := by dsimp only [w]; ring
      omega
    have hterm_le : n + (h + 1) * n * (2 + 2 ^ (w' + 2)) ≤ (h + 1) * n * (4 * 2 ^ w) := by
      have h1 : n ≤ (h + 1) * n * 2 ^ w := by
        have : 1 ≤ (h + 1) * 2 ^ w := Nat.mul_pos (by omega) (by omega)
        nlinarith
      have h2 : (h + 1) * n * (2 + 2 ^ (w' + 2)) ≤ (h + 1) * n * (3 * 2 ^ w) :=
        Nat.mul_le_mul_left ((h + 1) * n) hK_le
      nlinarith
    have h16 : 2 ^ w * 8 ^ w = 16 ^ w := by
      calc 2 ^ w * 8 ^ w = (2 * 8) ^ w := (Nat.mul_pow 2 8 w).symm
        _ = 16 ^ w := rfl
    have hcost_16 : stCost st2 ≤ 108 * n * (h + 1) * 16 ^ w := by
      calc stCost st2 ≤ (n + (h + 1) * n * (2 + 2 ^ (w' + 2))) * unitCost w' := hcost_total
        _ ≤ ((h + 1) * n * (4 * 2 ^ w)) * (27 * 8 ^ w) :=
          Nat.mul_le_mul_right (unitCost w') hterm_le
        _ = 108 * n * (h + 1) * (2 ^ w * 8 ^ w) := by ring
        _ = 108 * n * (h + 1) * 16 ^ w := by rw [h16]
    have h16pos : 1 ≤ 16 ^ w := Nat.one_le_pow w 16 (by omega)
    have hhp : 1 ≤ h + 1 := by omega
    have hst2_eq : m + 3 * st2.2.length = 1 + stCost st2 := by
      simp only [m, stCost]; omega
    have hbound : 1 + 108 * n * (h + 1) * 16 ^ w ≤ 256 * (n + 1) * (h + 1) * 16 ^ w := by
      have h1 : 1 ≤ (h + 1) * 16 ^ w := Nat.mul_pos hhp h16pos
      nlinarith
    change m + (∑ D ∈ Ffin, D.card) ≤ 256 * (n + 1) * (h + 1) * 16 ^ w
    omega

end PEqualNP.Outside.L_pcx_235

theorem PEqualNP.Outside.L_pcx_235 : ∀ (n w : ℕ) (hn : 0 < n),
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
  let height := Nat.clog 2 n
  let rounds := if w = 0 then 1 else w * (height + 1)
  (∃ m F, enc rounds m F ∧
    m + (∑ D ∈ F, D.card) ≤ 256 * (n + 1) * (height + 1) * 16 ^ w) ∧
    (w ≤ 1 → ∀ d m F, enc d m F → rounds ≤ d) := by
  intro n w hn
  cases w with
  | zero =>
    constructor
    · obtain ⟨m, F, h1, h2, h3, h4⟩ := PEqualNP.Outside.L_pcx_235.upper_bound_w0 n hn
      exact ⟨m, F, ⟨h1, h2, h3⟩, h4⟩
    · intro _ d m F ⟨_, _, hρ⟩
      exact PEqualNP.Outside.L_pcx_235.lower_bound_w0 hn F (fun ρ hcomp => (hρ ρ).2 hcomp)
  | succ w' =>
    constructor
    · obtain ⟨m, F, h1, h2, h3, h4⟩ := PEqualNP.Outside.L_pcx_235.upper_bound_wsucc n w' hn
      exact ⟨m, F, ⟨h1, h2, h3⟩, h4⟩
    · intro hw d m F ⟨hcard, _, hρ⟩
      have hw0 : w' = 0 := by omega
      subst hw0
      have hlb := PEqualNP.Outside.L_pcx_235.lower_bound_w1 hn F hcard (fun ρ hcomp => (hρ ρ).2 hcomp)
      simpa using hlb
