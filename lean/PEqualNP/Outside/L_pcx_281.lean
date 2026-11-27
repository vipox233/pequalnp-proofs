import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_281_aux
open PEqualNP.ProofComplexity

private theorem derivation_witness {V : Type} [DecidableEq V] {F : Set (Clause V)}
    {π : List (Clause V)} (hπ : IsDerivation F π) :
    ∃ step : Fin π.length → Option (Fin π.length × Fin π.length),
      ∀ i : Fin π.length,
        match step i with
        | none => π[i] ∈ F
        | some (j, k) => i.val < j.val ∧ i.val < k.val ∧ IsResolvent π[j] π[k] π[i] := by
  induction hπ with
  | nil =>
    exact ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | @ax π C _ hCF ih =>
    obtain ⟨step, hstep⟩ := ih
    refine ⟨fun i => Fin.cases none (fun i' => (step i').map (fun p => (p.1.succ, p.2.succ))) i, ?_⟩
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa using hCF
    · intro i'
      have hi' := hstep i'
      cases hsi : step i' with
      | none =>
        rw [hsi] at hi'
        simpa [hsi] using hi'
      | some p =>
        rw [hsi] at hi'
        simpa [hsi] using hi'
  | @res π C D R _ hC hD hres ih =>
    obtain ⟨step, hstep⟩ := ih
    obtain ⟨j0, hj0⟩ := List.getElem_of_mem hC
    obtain ⟨k0, hk0⟩ := List.getElem_of_mem hD
    let j : Fin π.length := ⟨j0, hj0.1⟩
    let k : Fin π.length := ⟨k0, hk0.1⟩
    refine ⟨fun i => Fin.cases (some (j.succ, k.succ))
      (fun i' => (step i').map (fun p => (p.1.succ, p.2.succ))) i, ?_⟩
    intro i
    refine Fin.cases ?_ ?_ i
    · simp only [Fin.cases_zero, Fin.val_zero, Fin.val_succ, Nat.zero_lt_succ, true_and]
      change IsResolvent π[j] π[k] R
      have h1 : π[j] = C := hj0.2
      have h2 : π[k] = D := hk0.2
      rw [h1, h2]
      exact hres
    · intro i'
      have hi' := hstep i'
      cases hsi : step i' with
      | none =>
        rw [hsi] at hi'
        simpa [hsi] using hi'
      | some p =>
        rw [hsi] at hi'
        simpa [hsi] using hi'

private theorem resolvent_sound {V : Type} [DecidableEq V] {a : V → Bool}
    {C D R : Clause V} (hR : IsResolvent C D R) (hC : ClauseSat a C) (hD : ClauseSat a D) :
    ClauseSat a R := by
  obtain ⟨v, _, _, rfl⟩ := hR
  cases hav : a v with
  | false =>
    obtain ⟨l, hlC, hla⟩ := hC
    refine ⟨l, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨?_, hlC⟩), hla⟩
    intro heq; rw [heq] at hla; simp [hav] at hla
  | true =>
    obtain ⟨l, hlD, hla⟩ := hD
    refine ⟨l, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨?_, hlD⟩), hla⟩
    intro heq; rw [heq] at hla; simp [hav] at hla

private theorem unsat_core_of_refutation {V : Type} [DecidableEq V] {F : Set (Clause V)}
    {π : List (Clause V)} (href : IsRefutation F π) :
    ∃ S : Finset (Clause V),
      (∀ C ∈ S, C ∈ F ∧ C ∈ π) ∧
      (∀ a : V → Bool, ¬ ∀ C ∈ S, ClauseSat a C) ∧
      2 * S.card ≤ π.length + 1 := by
  classical
  obtain ⟨hπ, hempty⟩ := href
  obtain ⟨step, hstep⟩ := derivation_witness hπ
  obtain ⟨r0, hr0_lt, hr0_eq⟩ := List.getElem_of_mem hempty
  let r : Fin π.length := ⟨r0, hr0_lt⟩
  let Closed : Finset (Fin π.length) → Prop := fun U =>
    r ∈ U ∧ ∀ i ∈ U, ∀ j k, step i = some (j, k) → j ∈ U ∧ k ∈ U
  have hexU : ∃ n, ∃ U : Finset (Fin π.length), Closed U ∧ U.card = n :=
    ⟨Finset.univ.card, Finset.univ, ⟨Finset.mem_univ r, fun _ _ _ _ _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩⟩, rfl⟩
  let minCard := Nat.find hexU
  obtain ⟨U, hU_closed, hU_card⟩ := Nat.find_spec hexU
  let Uax := U.filter (fun i => (step i).isNone)
  let Ures := U.filter (fun i => (step i).isSome)
  have hpart : Uax.card + Ures.card = U.card := by
    have hdisj : Disjoint Uax Ures := by
      rw [Finset.disjoint_left]
      intro i h1 h2
      have ha := (Finset.mem_filter.mp h1).2
      have hr := (Finset.mem_filter.mp h2).2
      cases h : step i <;> simp [h] at ha hr
    have hunion : Uax ∪ Ures = U := by
      ext i
      simp only [Uax, Ures, Finset.mem_union, Finset.mem_filter]
      cases step i <;> simp
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have hcover : U.erase r ⊆ Ures.biUnion (fun i =>
      match step i with | none => ∅ | some (j, k) => ({j, k} : Finset (Fin π.length))) := by
    intro u hu
    obtain ⟨hne, huU⟩ := Finset.mem_erase.mp hu
    by_contra hnot
    have hclosed_erase : Closed (U.erase u) := by
      refine ⟨Finset.mem_erase.mpr ⟨Ne.symm hne, hU_closed.1⟩, ?_⟩
      intro i hi j k hsi
      have hiU : i ∈ U := Finset.mem_of_mem_erase hi
      obtain ⟨hjU, hkU⟩ := hU_closed.2 i hiU j k hsi
      have hiRes : i ∈ Ures := Finset.mem_filter.mpr ⟨hiU, by simp [hsi]⟩
      have hju : j ≠ u := by
        intro heq; subst heq
        exact hnot (Finset.mem_biUnion.mpr ⟨i, hiRes, by simp [hsi]⟩)
      have hku : k ≠ u := by
        intro heq; subst heq
        exact hnot (Finset.mem_biUnion.mpr ⟨i, hiRes, by simp [hsi]⟩)
      exact ⟨Finset.mem_erase.mpr ⟨hju, hjU⟩, Finset.mem_erase.mpr ⟨hku, hkU⟩⟩
    have hlt : (U.erase u).card < minCard := by
      dsimp only [minCard]
      rw [← hU_card]; exact Finset.card_erase_lt_of_mem huU
    exact Nat.find_min hexU hlt ⟨U.erase u, hclosed_erase, rfl⟩
  have hbound_erase : (U.erase r).card ≤ 2 * Ures.card := by
    calc (U.erase r).card
        ≤ (Ures.biUnion (fun i => match step i with | none => ∅ | some (j, k) => {j, k})).card :=
          Finset.card_le_card hcover
      _ ≤ ∑ i ∈ Ures, (match step i with | none => (∅ : Finset (Fin π.length)) | some (j, k) => {j, k}).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ Ures, 2 := by
          apply Finset.sum_le_sum
          intro i _
          cases step i with
          | none => simp
          | some p => exact Finset.card_le_two
      _ = 2 * Ures.card := by simp [mul_comm]
  have hr_card : (U.erase r).card = U.card - 1 := Finset.card_erase_of_mem hU_closed.1
  have hU_pos : 1 ≤ U.card := Finset.one_le_card.mpr ⟨r, hU_closed.1⟩
  have hU_le : U.card ≤ π.length := by
    calc U.card ≤ (Finset.univ : Finset (Fin π.length)).card := Finset.card_le_univ U
      _ = π.length := Fintype.card_fin π.length
  have h2ax : 2 * Uax.card ≤ π.length + 1 := by omega
  let S : Finset (Clause V) := Uax.image (fun i => π[i])
  refine ⟨S, ?_, ?_, ?_⟩
  · intro C hC
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hC
    have hi_none : (step i).isNone = true := (Finset.mem_filter.mp hi).2
    have hsi := hstep i
    cases h : step i with
    | none =>
      rw [h] at hsi
      exact ⟨hsi, List.getElem_mem i.isLt⟩
    | some _ => simp [h] at hi_none
  · intro a ha
    have hsat : ∀ d : ℕ, ∀ i : Fin π.length, π.length - 1 - i.val ≤ d → i ∈ U → ClauseSat a π[i] := by
      intro d
      induction d with
      | zero =>
        intro i hd hiU
        have hsi := hstep i
        cases h : step i with
        | none =>
          have hiAx : i ∈ Uax := Finset.mem_filter.mpr ⟨hiU, by simp [h]⟩
          exact ha π[i] (Finset.mem_image.mpr ⟨i, hiAx, rfl⟩)
        | some p =>
          rw [h] at hsi
          omega
      | succ d ih =>
        intro i hd hiU
        have hsi := hstep i
        cases h : step i with
        | none =>
          have hiAx : i ∈ Uax := Finset.mem_filter.mpr ⟨hiU, by simp [h]⟩
          exact ha π[i] (Finset.mem_image.mpr ⟨i, hiAx, rfl⟩)
        | some p =>
          rw [h] at hsi
          obtain ⟨hij, hik, hres⟩ := hsi
          obtain ⟨hjU, hkU⟩ := hU_closed.2 i hiU p.1 p.2 h
          exact resolvent_sound hres (ih p.1 (by omega) hjU) (ih p.2 (by omega) hkU)
    have hrempty : ClauseSat a π[r] := hsat π.length r (by omega) hU_closed.1
    have hrval : π[r] = ∅ := hr0_eq
    rw [hrval] at hrempty
    obtain ⟨l, hl, _⟩ := hrempty
    exact Finset.notMem_empty l hl
  · have hScard : S.card ≤ Uax.card := Finset.card_image_le
    omega

theorem extractCore {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool) :
    let cl := fun p : Fin m × Bool =>
      ({(left p.1, !p.2), (right p.1, p.2 ^^ sign p.1)} : Clause (Fin n))
    ∀ {π : List (Clause (Fin n))}, IsRefutation (Set.range cl) π →
      ∃ S : Finset (Fin m × Bool), Set.InjOn cl (S : Set (Fin m × Bool)) ∧
        (∀ p ∈ S, cl p ∈ π) ∧ 2*S.card ≤ π.length+1 ∧
        ∀ x : Fin n → Bool, ((S.filter (fun p =>
          x (right p.1) ≠ (x (left p.1) ^^ sign p.1))).filter
          (fun p => x (left p.1) = p.2)).Nonempty := by
  classical
  intro cl π href
  obtain ⟨T, hT, hunsat, hcard⟩ := unsat_core_of_refutation href
  let rep : (C : ↥T) → Fin m × Bool := fun C => Classical.choose (hT C C.property).1
  have hrep (C : ↥T) : cl (rep C) = C.val := Classical.choose_spec (hT C C.property).1
  let S := T.attach.image rep
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb he
    obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp (show a ∈ T.attach.image rep from ha)
    obtain ⟨B, _, rfl⟩ := Finset.mem_image.mp (show b ∈ T.attach.image rep from hb)
    exact congrArg rep (Subtype.ext ((hrep A).symm.trans (he.trans (hrep B))))
  · intro p hp
    obtain ⟨C, _, rfl⟩ := Finset.mem_image.mp hp
    rw [hrep]; exact (hT C C.property).2
  · have hle : S.card ≤ T.card := by simpa [S] using (Finset.card_image_le (s := T.attach) (f := rep))
    omega
  · intro x
    have h := hunsat x
    push_neg at h
    obtain ⟨C, hC, hmiss⟩ := h
    let p := rep ⟨C, hC⟩
    have hmem : p ∈ S := Finset.mem_image.mpr ⟨⟨C, hC⟩, T.mem_attach _, rfl⟩
    have he : cl p = C := hrep ⟨C, hC⟩
    rw [← he] at hmiss
    have hl : x (left p.1) ≠ !p.2 := fun hl =>
      hmiss ⟨(left p.1, !p.2), by simp [cl], hl⟩
    have hr : x (right p.1) ≠ (p.2 ^^ sign p.1) := fun hr =>
      hmiss ⟨(right p.1, p.2 ^^ sign p.1), by simp [cl], hr⟩
    have hl' : x (left p.1) = p.2 := by cases h₁ : x (left p.1) <;> cases h₂ : p.2 <;> simp_all
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hmem, by rwa [hl']⟩, hl'⟩⟩

end PEqualNP.Outside.L_pcx_281_aux

namespace PEqualNP.Outside.L_pcx_281_aux

private def xorPrefix (s : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | k + 1 => xorPrefix s k ^^ s k

private theorem xorPrefix_eq_true_iff_odd (s : ℕ → Bool) (m : ℕ) :
    xorPrefix s m = true ↔ Odd (((Finset.range m).filter (fun i => s i = true)).card) := by
  induction m with
  | zero =>
    simp [xorPrefix]
  | succ m ih =>
    have hfilt : (Finset.range (m + 1)).filter (fun i => s i = true) =
        if s m = true then insert m ((Finset.range m).filter (fun i => s i = true))
        else (Finset.range m).filter (fun i => s i = true) := by
      rw [Finset.range_add_one, Finset.filter_insert]
    have hnotmem : m ∉ (Finset.range m).filter (fun i => s i = true) := by
      simp
    rw [hfilt, xorPrefix]
    cases hsm : s m
    · simp only [Bool.false_eq_true, ite_false, Bool.xor_false]
      exact ih
    · simp only [ite_true, Finset.card_insert_of_notMem hnotmem, Bool.xor_true]
      constructor
      · intro hnot
        have hf : xorPrefix s m = false := by cases hc : xorPrefix s m <;> simp_all
        have hneven : ¬ Odd (((Finset.range m).filter (fun i => s i = true)).card) := by
          rw [← ih, hf]; decide
        rcases Nat.even_or_odd (((Finset.range m).filter (fun i => s i = true)).card) with he | ho
        · rcases he with ⟨k, hk⟩
          exact ⟨k, by omega⟩
        · exact absurd ho hneven
      · rintro ⟨k, hk⟩
        cases hc : xorPrefix s m
        · rfl
        · rcases ih.mp hc with ⟨j, hj⟩
          omega

private def badCycle {n : ℕ} (E : Fin n → Fin n → Bool → Prop) (m : ℕ) : Prop :=
  ∃ (v : ℕ → Fin n) (s : ℕ → Bool),
    v 0 = v m ∧ Odd (((Finset.range m).filter (fun i => s i = true)).card) ∧
    ∀ i < m, E (v i) (v (i + 1)) (s i)

private def HasEdge {n : ℕ} (es : List (Fin n × Fin n × Bool)) (u v : Fin n) (b : Bool) : Prop :=
  (u, v, b) ∈ es ∨ (v, u, b) ∈ es

private def WalkIn {n : ℕ} (es : List (Fin n × Fin n × Bool)) (u v : Fin n) (d : ℕ) : Prop :=
  ∃ (vs : ℕ → Fin n) (ss : ℕ → Bool),
    vs 0 = u ∧ vs d = v ∧ ∀ i < d, HasEdge es (vs i) (vs (i + 1)) (ss i)

private def Connected {n : ℕ} (es : List (Fin n × Fin n × Bool)) (u v : Fin n) : Prop :=
  ∃ d : ℕ, WalkIn es u v d

private theorem connected_refl {n : ℕ} (es : List (Fin n × Fin n × Bool)) (u : Fin n) :
    Connected es u u :=
  ⟨0, fun _ => u, fun _ => false, rfl, rfl, fun i hi => by omega⟩

private theorem connected_step {n : ℕ} (es : List (Fin n × Fin n × Bool)) {u v w : Fin n} {b : Bool}
    (huv : Connected es u v) (hvw : HasEdge es v w b) : Connected es u w := by
  rcases huv with ⟨d, vs, ss, hv0, hvd, hstep⟩
  refine ⟨d + 1, fun i => if i ≤ d then vs i else w, fun i => if i < d then ss i else b,
    by simp [hv0], by simp, ?_⟩
  intro i hi
  by_cases hid : i < d
  · have h1 : i ≤ d := by omega
    have h2 : i + 1 ≤ d := by omega
    simp only [h1, h2, hid, ite_true]
    exact hstep i hid
  · have hieq : i = d := by omega
    rw [hieq]
    simp only [Nat.le_refl, ite_true, show ¬ (d + 1 ≤ d) by omega, ite_false,
      show ¬ (d < d) by omega, hvd]
    exact hvw

private theorem walk_eval {n : ℕ} {es : List (Fin n × Fin n × Bool)} {φ : Fin n → Bool}
    (hφ : ∀ e ∈ es, (φ e.1 ^^ φ e.2.1) = e.2.2)
    {vs : ℕ → Fin n} {ss : ℕ → Bool} (d : ℕ)
    (hstep : ∀ i < d, HasEdge es (vs i) (vs (i + 1)) (ss i)) :
    (φ (vs 0) ^^ φ (vs d)) = xorPrefix ss d := by
  induction d with
  | zero => simp [xorPrefix]
  | succ d ih =>
    have hprev := ih (fun i hi => hstep i (by omega))
    have hlast : (φ (vs d) ^^ φ (vs (d + 1))) = ss d := by
      rcases hstep d (Nat.lt_succ_self d) with h1 | h2
      · exact hφ _ h1
      · have h := hφ _ h2
        rw [Bool.xor_comm] at h
        exact h
    rw [xorPrefix, ← hprev, ← hlast]
    cases φ (vs 0) <;> cases φ (vs d) <;> cases φ (vs (d + 1)) <;> rfl

private theorem shortest_walk_nodup {n : ℕ} {es : List (Fin n × Fin n × Bool)} {u v : Fin n} {d : ℕ}
    (hmin : ∀ d' < d, ¬ WalkIn es u v d')
    {vs : ℕ → Fin n} {ss : ℕ → Bool}
    (hv0 : vs 0 = u) (hvd : vs d = v)
    (hstep : ∀ i < d, HasEdge es (vs i) (vs (i + 1)) (ss i)) :
    ∀ p q : ℕ, p ≤ d → q ≤ d → vs p = vs q → p = q := by
  intro p q hp hq hpq
  by_contra hne
  wlog hlt : p < q generalizing p q
  · exact this q p hq hp hpq.symm (Ne.symm hne) (by omega)
  let d' := d - (q - p)
  have hd' : d' < d := by omega
  apply hmin d' hd'
  refine ⟨fun i => if i ≤ p then vs i else vs (i + (q - p)),
    fun i => if i < p then ss i else ss (i + (q - p)), ?_, ?_, ?_⟩
  · simp [hv0]
  · by_cases hdp : d' ≤ p
    · have hqd : q = d ∧ p = d' := by omega
      simp only [hdp, ite_true]
      rw [← hqd.2, hpq, hqd.1, hvd]
    · simp only [hdp, ite_false]
      have : d' + (q - p) = d := by omega
      rw [this, hvd]
  · intro i hi
    by_cases hip : i < p
    · have h1 : i ≤ p := by omega
      have h2 : i + 1 ≤ p := by omega
      simp only [h1, h2, hip, ite_true]
      exact hstep i (by omega)
    · by_cases hieq : i = p
      · subst hieq
        simp only [Nat.le_refl, ite_true, show ¬ (i + 1 ≤ i) by omega, ite_false,
          show ¬ (i < i) by omega]
        have h1 : i + 1 + (q - i) = q + 1 := by omega
        have h2 : i + (q - i) = q := by omega
        rw [h1, h2, hpq]
        exact hstep q (by omega)
      · have h1 : ¬ (i ≤ p) := by omega
        have h2 : ¬ (i + 1 ≤ p) := by omega
        have h3 : ¬ (i < p) := by omega
        simp only [h1, h2, h3, ite_false]
        have h4 : i + 1 + (q - p) = (i + (q - p)) + 1 := by omega
        rw [h4]
        exact hstep (i + (q - p)) (by omega)

private theorem shortest_walk_le_len {n : ℕ} {es : List (Fin n × Fin n × Bool)} {u v : Fin n} {d : ℕ}
    (hmin : ∀ d' < d, ¬ WalkIn es u v d')
    {vs : ℕ → Fin n} {ss : ℕ → Bool}
    (hv0 : vs 0 = u) (hvd : vs d = v)
    (hstep : ∀ i < d, HasEdge es (vs i) (vs (i + 1)) (ss i)) :
    d ≤ es.length := by
  have hinj := shortest_walk_nodup hmin hv0 hvd hstep
  have hex : ∀ i : Fin d, ∃ k : Fin es.length,
      es[k.val] = (vs i.val, vs (i.val + 1), ss i.val) ∨
      es[k.val] = (vs (i.val + 1), vs i.val, ss i.val) := by
    intro i
    rcases hstep i.val i.isLt with h1 | h2
    · rcases List.mem_iff_getElem.mp h1 with ⟨k, hk, hget⟩
      exact ⟨⟨k, hk⟩, Or.inl hget⟩
    · rcases List.mem_iff_getElem.mp h2 with ⟨k, hk, hget⟩
      exact ⟨⟨k, hk⟩, Or.inr hget⟩
  choose f hf using hex
  have hfinj : Function.Injective f := by
    intro i j hij
    have hi := hf i
    have hj := hf j
    rw [hij] at hi
    rcases hi with hi | hi <;> rcases hj with hj | hj
    · have heq := hi.symm.trans hj
      have h1 : vs i.val = vs j.val := congrArg Prod.fst heq
      exact Fin.ext (hinj i.val j.val (by omega) (by omega) h1)
    · have heq := hi.symm.trans hj
      have h1 : vs i.val = vs (j.val + 1) := congrArg Prod.fst heq
      have h2 : vs (i.val + 1) = vs j.val := congrArg (fun x => x.2.1) heq
      have e1 := hinj i.val (j.val + 1) (by omega) (by omega) h1
      have e2 := hinj (i.val + 1) j.val (by omega) (by omega) h2
      omega
    · have heq := hi.symm.trans hj
      have h1 : vs (i.val + 1) = vs j.val := congrArg Prod.fst heq
      have h2 : vs i.val = vs (j.val + 1) := congrArg (fun x => x.2.1) heq
      have e1 := hinj (i.val + 1) j.val (by omega) (by omega) h1
      have e2 := hinj i.val (j.val + 1) (by omega) (by omega) h2
      omega
    · have heq := hi.symm.trans hj
      have h1 : vs (i.val + 1) = vs (j.val + 1) := congrArg Prod.fst heq
      have e1 := hinj (i.val + 1) (j.val + 1) (by omega) (by omega) h1
      exact Fin.ext (by omega)
  have hcard := Fintype.card_le_of_injective f hfinj
  simpa using hcard

private theorem consistent_or_bad {n : ℕ} (E : Fin n → Fin n → Bool → Prop)
    (hsym : ∀ u v b, E u v b → E v u b) (es : List (Fin n × Fin n × Bool))
    (hE : ∀ e ∈ es, E e.1 e.2.1 e.2.2) :
    (∃ φ : Fin n → Bool, ∀ e ∈ es, (φ e.1 ^^ φ e.2.1) = e.2.2) ∨
    (∃ j ≤ es.length, badCycle E j) := by
  classical
  induction es with
  | nil =>
    left
    exact ⟨fun _ => false, fun _ h => by simp at h⟩
  | cons e rest ih =>
    rcases e with ⟨u, v, b⟩
    have hE_e : E u v b := hE (u, v, b) (by simp)
    have hE_rest : ∀ e' ∈ rest, E e'.1 e'.2.1 e'.2.2 := fun e' he' => hE e' (by simp [he'])
    rcases ih hE_rest with ⟨φ, hφ⟩ | ⟨j, hj, hbad⟩
    · by_cases hconn : Connected rest u v
      · by_cases hsat : (φ u ^^ φ v) = b
        · left
          refine ⟨φ, fun e' he' => ?_⟩
          simp only [List.mem_cons] at he'
          rcases he' with rfl | hr
          · exact hsat
          · exact hφ e' hr
        · right
          let d := Nat.find hconn
          have hd_walk : WalkIn rest u v d := Nat.find_spec hconn
          have hd_min : ∀ d' < d, ¬ WalkIn rest u v d' := fun d' hd' => Nat.find_min hconn hd'
          rcases hd_walk with ⟨vs, ss, hv0, hvd, hstep⟩
          have hd_le : d ≤ rest.length := shortest_walk_le_len hd_min hv0 hvd hstep
          have hpar := walk_eval hφ d hstep
          rw [hv0, hvd] at hpar
          refine ⟨d + 1, by simp; omega, ?_⟩
          let vs' : ℕ → Fin n := fun i => if i ≤ d then vs i else u
          let ss' : ℕ → Bool := fun i => if i < d then ss i else b
          refine ⟨vs', ss', by simp [vs', hv0], ?_, ?_⟩
          · rw [← xorPrefix_eq_true_iff_odd]
            have hpre : xorPrefix ss' d = xorPrefix ss d := by
              have hgen : ∀ k ≤ d, xorPrefix ss' k = xorPrefix ss k := by
                intro k hk
                induction k with
                | zero => rfl
                | succ k ihk =>
                  simp only [xorPrefix, ihk (by omega), ss', show k < d by omega, ite_true]
              exact hgen d (Nat.le_refl d)
            rw [xorPrefix, hpre]
            simp only [ss', show ¬ (d < d) by omega, ite_false]
            rw [← hpar]
            cases hc : (φ u ^^ φ v) <;> cases hb : b <;> simp_all
          · intro i hi
            by_cases hid : i < d
            · simp only [vs', ss', show i ≤ d by omega, show i + 1 ≤ d by omega, hid, ite_true]
              rcases hstep i hid with h1 | h2
              · exact hE_rest _ h1
              · exact hsym _ _ _ (hE_rest _ h2)
            · have hieq : i = d := by omega
              subst hieq
              simp only [vs', ss', Nat.le_refl, ite_true, show ¬ (d + 1 ≤ d) by omega, ite_false,
                show ¬ (d < d) by omega, hvd]
              exact hsym u v b hE_e
      · left
        let delta : Bool := (φ u ^^ φ v) ^^ b
        let φ' : Fin n → Bool := fun z => if Connected rest u z then φ z ^^ delta else φ z
        refine ⟨φ', fun e' he' => ?_⟩
        simp only [List.mem_cons] at he'
        rcases he' with rfl | hr
        · simp only [φ', connected_refl rest u, ite_true, hconn, ite_false, delta]
          cases φ u <;> cases φ v <;> cases b <;> rfl
        · rcases e' with ⟨x, y, b'⟩
          have hxy : Connected rest u x ↔ Connected rest u y :=
            ⟨fun hx => connected_step rest hx (Or.inl hr),
             fun hy => connected_step rest hy (Or.inr hr)⟩
          have hbase : (φ x ^^ φ y) = b' := hφ (x, y, b') hr
          dsimp only [φ']
          by_cases hcx : Connected rest u x
          · have hcy : Connected rest u y := hxy.mp hcx
            simp only [hcx, hcy, ite_true, ← hbase]
            cases φ x <;> cases φ y <;> cases delta <;> rfl
          · have hcy : ¬ Connected rest u y := fun h => hcx (hxy.mpr h)
            simp only [hcx, hcy, ite_false]
            exact hbase
    · right
      exact ⟨j, by simp; omega, hbad⟩

theorem small_consistent {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool)
    {g : ℕ} (hmin : ∀ k < g, ¬ ∃ (v : ℕ → Fin n) (edge : ℕ → Fin m),
      v 0 = v k ∧ Odd (((Finset.range k).filter (fun j => sign (edge j) = true)).card) ∧
      ∀ j < k, (v j = left (edge j) ∧ v (j+1) = right (edge j)) ∨
        (v j = right (edge j) ∧ v (j+1) = left (edge j)))
    (T : Finset (Fin m × Bool)) (hT : T.card < g) :
    ∃ x : Fin n → Bool, ∀ p ∈ T, x (right p.1) = (x (left p.1) ^^ sign p.1) := by
  classical
  rcases T.eq_empty_or_nonempty with rfl | ⟨p₀, _⟩
  · exact ⟨fun _ => false, by simp⟩
  let E := fun u v b => ∃ i : Fin m, sign i = b ∧
    ((u = left i ∧ v = right i) ∨ (u = right i ∧ v = left i))
  let triple := fun p : Fin m × Bool => (left p.1, right p.1, sign p.1)
  let es := T.toList.map triple
  have hsym : ∀ u v b, E u v b → E v u b := by
    rintro u v b ⟨i, hi, ⟨hu,hv⟩ | ⟨hu,hv⟩⟩
    · exact ⟨i, hi, Or.inr ⟨hv, hu⟩⟩
    · exact ⟨i, hi, Or.inl ⟨hv, hu⟩⟩
  have he : ∀ e ∈ es, E e.1 e.2.1 e.2.2 := by
    intro e he
    rcases List.mem_map.mp he with ⟨p, _, rfl⟩
    exact ⟨p.1, rfl, Or.inl ⟨rfl, rfl⟩⟩
  rcases consistent_or_bad E hsym es he with ⟨x, hx⟩ | ⟨k, hk, v, s, hv, hodd, hwalk⟩
  · refine ⟨x, fun p hp => ?_⟩
    have h : (x (left p.1) ^^ x (right p.1)) = sign p.1 :=
      hx (triple p) (List.mem_map.mpr ⟨p, Finset.mem_toList.mpr hp, rfl⟩)
    rw [← h, ← Bool.xor_assoc]; simp
  · have hlen : es.length = T.card := by simp [es]
    exfalso
    apply hmin k (by omega)
    let edge : ℕ → Fin m := fun j => if hj : j < k then (hwalk j hj).choose else p₀.1
    have hspec (j : ℕ) (hj : j < k) : sign (edge j) = s j ∧
        ((v j = left (edge j) ∧ v (j+1) = right (edge j)) ∨
        (v j = right (edge j) ∧ v (j+1) = left (edge j))) := by
      simpa only [edge, dif_pos hj] using (hwalk j hj).choose_spec
    refine ⟨v, edge, hv, ?_, fun j hj => (hspec j hj).2⟩
    have hf : (Finset.range k).filter (fun j => sign (edge j) = true) =
        (Finset.range k).filter (fun j => s j = true) := by
      apply Finset.filter_congr
      intro j hj
      rw [(hspec j (Finset.mem_range.mp hj)).1]
    rw [hf]; exact hodd

end PEqualNP.Outside.L_pcx_281_aux

namespace PEqualNP.Outside.L_pcx_281_aux
open scoped BigOperators
abbrev Bit := ZMod 2
private def enc (b : Bool) : Bit := if b then 1 else 0
private def dec (z : Bit) : Bool := decide (z = 1)
private theorem enc_xor (b c : Bool) : enc (b ^^ c) = enc b + enc c := by cases b <;> cases c <;> decide
private theorem bit_cases (z : Bit) : z = 0 ∨ z = 1 := by fin_cases z <;> first | exact Or.inl rfl | exact Or.inr rfl
private theorem dec_fault (a c y : Bit) (b : Bool) : a - c = y - enc b →
    ((dec a ≠ (dec c ^^ b)) ↔ y = 1) := by
  rcases bit_cases a with rfl|rfl <;> rcases bit_cases c with rfl|rfl <;> rcases bit_cases y with rfl|rfl <;> cases b <;> decide
variable {I V : Type} [Fintype I] [DecidableEq I]
def diffMap (l r : I → V) : (V → Bit) →ₗ[Bit] (I → Bit) where
  toFun x i := x (r i) - x (l i)
  map_add' x y := by ext i; simp; abel
  map_smul' a x := by ext i; simp [mul_sub]
abbrev Sig (l r : I → V) := (I → Bit) ⧸ LinearMap.range (diffMap l r)
noncomputable def col (l r : I → V) (i : I) : Sig l r := (LinearMap.range (diffMap l r)).mkQ (Pi.single i 1)
noncomputable def target (l r : I → V) (b : I → Bool) : Sig l r := (LinearMap.range (diffMap l r)).mkQ (fun i => enc (b i))
private theorem single_sum (v : I → Bit) : (∑ i, v i • (Pi.single i 1 : I → Bit)) = v := by
  ext j
  rw [Finset.sum_apply, Fintype.sum_eq_single j]
  · simp
  · intro i h; simp [Pi.single_eq_of_ne (Ne.symm h)]
private theorem eval_expand (l r : I → V) (h : Sig l r →ₗ[Bit] Bit) (v : I → Bit) :
    h ((LinearMap.range (diffMap l r)).mkQ v) = ∑ i, v i * h (col l r i) := by
  conv_lhs => rw [← single_sum v]
  simp [map_sum, col]
private theorem diff_zero (l r : I → V) (x : V → Bit) :
    (LinearMap.range (diffMap l r)).mkQ (diffMap l r x) = 0 := by
  apply LinearMap.mem_ker.mp; rw [Submodule.ker_mkQ]; exact ⟨x,rfl⟩
private theorem eq_on_good (l r : I → V) (b : I → Bool) (x : V → Bool) (i : I)
    (hi : x (r i) = (x (l i) ^^ b i)) : diffMap l r (fun v => enc (x v)) i = enc (b i) := by
  change enc (x (r i)) - enc (x (l i)) = _
  rw [hi, enc_xor]; abel

theorem oddRowLarge (l r : I → V) (b : I → Bool) {g : ℕ}
    (small : ∀ A : Finset I, A.card < g → ∃ x : V → Bool, ∀ i ∈ A, x (r i) = (x (l i) ^^ b i))
    (h : Sig l r →ₗ[Bit] Bit) (hs : h (target l r b) = 1) :
    g ≤ (Finset.univ.filter fun i => h (col l r i) = 1).card := by
  classical
  by_contra! hlt
  obtain ⟨x,hx⟩ := small _ hlt
  have hz := congrArg h (diff_zero l r (fun v => enc (x v)))
  rw [map_zero, eval_expand] at hz
  rw [target, eval_expand] at hs
  have he : (∑ i, diffMap l r (fun v => enc (x v)) i * h (col l r i)) = ∑ i, enc (b i) * h (col l r i) := by
    apply Finset.sum_congr rfl; intro i _
    by_cases hi : h (col l r i) = 1
    · rw [eq_on_good l r b x i (hx i (by simpa using hi))]
    · have h0 := (bit_cases (h (col l r i))).resolve_right hi
      rw [h0, mul_zero, mul_zero]
  exact zero_ne_one ((hz.symm.trans he).trans hs)

theorem faultWord (l r : I → V) (b : I → Bool) (y : I → Bit)
    (hy : (LinearMap.range (diffMap l r)).mkQ y = target l r b) :
    ∃ x : V → Bool, ∀ i, (x (r i) ≠ (x (l i) ^^ b i)) ↔ y i = 1 := by
  classical
  have hh : y - (fun i => enc (b i)) ∈ LinearMap.range (diffMap l r) := by
    rw [← Submodule.ker_mkQ (LinearMap.range (diffMap l r)), LinearMap.mem_ker, map_sub, sub_eq_zero]; exact hy
  obtain ⟨a, ha⟩ := hh
  refine ⟨fun v => dec (a v), fun i => ?_⟩
  have e := congrFun ha i
  change a (r i) - a (l i) = y i - enc (b i) at e
  exact dec_fault _ _ _ _ e
end PEqualNP.Outside.L_pcx_281_aux

namespace PEqualNP.Outside.L_pcx_281_aux
namespace P281Graphic

open Finset

variable {V E O : Type*} [Fintype E]

def cut (l r : E → V) (x : V → Bool) (e : E) : Bool := decide (x (l e) ≠ x (r e))

noncomputable def weight (w : E → Bool) : ℕ := (univ.filter fun e => w e = true).card

noncomputable def words (l r : E → V) : Finset (E → Bool) := by
  classical exact univ.filter fun w => ∃ x, cut l r x = w

noncomputable def restrictedWords (l r : E → V) (a b : O → V) : Finset (E → Bool) := by
  classical exact univ.filter fun w => ∃ x, (∀ o, x (a o) = x (b o)) ∧ cut l r x = w

theorem contract_outside (l r : E → V) (a b : O → V) :
    let R := fun u v => ∃ o, a o = u ∧ b o = v
    let q := Quot.mk R
    restrictedWords l r a b = words (q ∘ l) (q ∘ r) := by
  classical
  intro R q
  ext w
  simp only [restrictedWords, words, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨Quot.lift x (fun u v huv => ?_), rfl⟩
    obtain ⟨o, rfl, rfl⟩ := huv
    exact hx o
  · rintro ⟨x, rfl⟩
    refine ⟨x ∘ q, fun o => congrArg x (Quot.sound ?_), rfl⟩
    exact ⟨o, rfl, rfl⟩

noncomputable def ends (l r : E → V) (e : E) : Finset V := by
  classical exact if l e = r e then ∅ else {l e, r e}

noncomputable def active (l r : E → V) : Finset V := by
  classical exact univ.biUnion (ends l r)

omit [Fintype E] in
private theorem singleton_crosses (l r : E → V) (v : V) (e : E) :
    (cut l r (fun u => @decide (u = v) (Classical.propDecidable _)) e = true) ↔
      v ∈ ends l r e := by
  classical
  by_cases h : l e = r e
  · simp [cut, ends, h]
  · simp only [cut, decide_eq_true_eq, ends, h, ↓reduceIte, mem_insert, mem_singleton]
    by_cases hl : l e = v <;> by_cases hr : r e = v <;> simp [hl, hr] <;> grind

theorem incidences_bound (l r : E → V) (d : ℕ)
    (hmin : ∀ w ∈ words l r, w ≠ (fun _ => false) → d ≤ weight w) :
    (active l r).card * d ≤ 2 * Fintype.card E := by
  classical
  let A := active l r
  let inc := fun v e => v ∈ ends l r e
  have degree (v) (hv : v ∈ A) : d ≤ (univ.filter (inc v)).card := by
    let w := cut l r (fun u => decide (u = v))
    have hw (e) : w e = true ↔ inc v e := singleton_crosses l r v e
    have hword : w ∈ words l r := by simpa [words] using (show ∃ x, cut l r x = w from ⟨_, rfl⟩)
    obtain ⟨e, _, he⟩ := mem_biUnion.mp (show v ∈ univ.biUnion (ends l r) from hv)
    have ne : w ≠ (fun _ => false) := by
      intro eq
      have := (hw e).2 he
      simp [eq] at this
    simpa only [weight, hw] using hmin w hword ne
  calc
    A.card * d = ∑ _v ∈ A, d := by simp
    _ ≤ ∑ v ∈ A, (univ.filter (inc v)).card := sum_le_sum degree
    _ = ∑ v ∈ A, ∑ e : E, if inc v e then 1 else 0 := by simp [sum_boole]
    _ = ∑ e : E, ∑ v ∈ A, if inc v e then 1 else 0 := sum_comm
    _ ≤ ∑ _e : E, 2 := by
      apply sum_le_sum
      intro e _
      rw [sum_boole, Nat.cast_id]
      calc
        _ ≤ (ends l r e).card := card_le_card (fun v hv => (mem_filter.mp hv).2)
        _ ≤ 2 := by by_cases h : l e = r e <;> simp [ends, h]
    _ = 2 * Fintype.card E := by simp [Nat.mul_comm]

theorem few_vertex_words (l r : E → V) (h : (active l r).card ≤ 3) :
    (words l r).card ≤ 4 := by
  classical
  let A := active l r
  obtain ⟨B, hB, hbase⟩ : ∃ B : Finset V, B.card ≤ 2 ∧
      ∀ x : V → Bool, ∃ base : Bool, ∀ v ∈ A, v ∉ B → x v = base := by
    rcases A.eq_empty_or_nonempty with he | ⟨v, hv⟩
    · exact ⟨∅, by simp, fun x => ⟨false, by simp [he]⟩⟩
    · refine ⟨A.erase v, ?_, fun x => ⟨x v, ?_⟩⟩
      · rw [card_erase_of_mem hv]; change A.card ≤ 3 at h; omega
      · intro u hu hn
        have : u = v := by simpa [mem_erase, hu] using hn
        rw [this]
  let extB := fun (y : B → Bool) (v : V) => if hv : v ∈ B then y ⟨v, hv⟩ else false
  let f := fun y => cut l r (extB y)
  have sub : words l r ⊆ univ.image f := by
    intro w hw
    obtain ⟨x, rfl⟩ : ∃ x, cut l r x = w := by simpa [words] using hw
    obtain ⟨base, hb⟩ := hbase x
    let y : B → Bool := fun v => decide (x v.val ≠ base)
    have hy (v) (hv : v ∈ A) : extB y v = decide (x v ≠ base) := by
      by_cases hm : v ∈ B <;> simp [extB, y, hm, hb v hv]
    refine mem_image.mpr ⟨y, mem_univ _, ?_⟩
    funext e
    by_cases he : l e = r e
    · simp [f, cut, he]
    · have ha (v) (hv : v ∈ ends l r e) : v ∈ A := mem_biUnion.mpr ⟨e, mem_univ _, hv⟩
      have hl := ha (l e) (by simp [ends, he])
      have hr := ha (r e) (by simp [ends, he])
      simp only [f, cut, hy _ hl, hy _ hr]
      cases x (l e) <;> cases x (r e) <;> cases base <;> decide
  calc
    _ ≤ (univ.image f).card := card_le_card sub
    _ ≤ (univ : Finset (B → Bool)).card := card_image_le
    _ = 2 ^ B.card := by simp
    _ ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) hB
    _ = 4 := rfl

theorem restricted_card_le_four (l r : E → V) (a b : O → V) (d : ℕ)
    (hsize : 2 * Fintype.card E < 4 * d)
    (hmin : ∀ w ∈ restrictedWords l r a b, w ≠ (fun _ => false) → d ≤ weight w) :
    (restrictedWords l r a b).card ≤ 4 := by
  rw [contract_outside] at hmin ⊢
  apply few_vertex_words
  have hb := incidences_bound _ _ d hmin
  by_contra! h
  have hh := Nat.mul_le_mul_right d (show 4 ≤ _ from h)
  omega

theorem cut_simplex_rank_le_two (l r : E → V) (a b : O → V) (t : ℕ)
    (hsize : Fintype.card E = 2 ^ t - 1)
    (hrank : 2 ^ t ≤ (restrictedWords l r a b).card)
    (hmin : ∀ w ∈ restrictedWords l r a b, w ≠ (fun _ => false) → 2 ^ (t-1) ≤ weight w) :
    t ≤ 2 := by
  by_contra! h
  have hp : 2 ^ t = 2 ^ (t-1) * 2 := by
    conv_lhs => rw [show t = (t-1)+1 by omega, pow_succ]
  have hd := restricted_card_le_four l r a b (2 ^ (t-1)) (by rw [hsize, hp]; have := Nat.two_pow_pos (t-1); omega) hmin
  have hh := Nat.pow_le_pow_right (n := 2) (by decide) (show 3 ≤ t from h)
  omega

theorem no_seven (l r : E → V) (a b : O → V) (hsize : Fintype.card E = 7)
    (hrank : 8 ≤ (restrictedWords l r a b).card)
    (hmin : ∀ w ∈ restrictedWords l r a b, w ≠ (fun _ => false) → 4 ≤ weight w) : False := by
  have := cut_simplex_rank_le_two l r a b 3 hsize hrank hmin
  omega

end P281Graphic
end PEqualNP.Outside.L_pcx_281_aux

namespace PEqualNP.Outside.L_pcx_281_aux
open Finset
abbrev Cube := Fin 3 → Bit
private def vec : Fin 7 → Cube :=
  ![![1,0,0], ![0,1,0], ![0,0,1], ![1,1,0], ![1,0,1], ![0,1,1], ![1,1,1]]
private def par (w : Fin 7 → Bool) : Bit := ∑ j, enc (w j)
private def syn (w : Fin 7 → Bool) : Cube := ∑ j, enc (w j) • vec j
private def good (w : Fin 7 → Bool) : Prop := par w = 0 ∧ syn w = 0
private instance (w : Fin 7 → Bool) : Decidable (good w) := inferInstanceAs (Decidable (_ ∧ _))
private def code := univ.filter good
set_option maxRecDepth 20000 in
set_option maxHeartbeats 900000 in
private theorem fanoFacts : code.card = 8 ∧
    (∀ w : Fin 7 → Bool, good w → w ≠ (fun _ => false) → 4 ≤ (univ.filter (fun j => w j = true)).card) ∧
    (∀ j, vec j ≠ 0) ∧ (∀ i j, vec i = vec j → i = j) := by decide +kernel

private theorem cut_iff {I V : Type} [Fintype I] [DecidableEq I]
    (l r : I → V) (e : Fin 7 ↪ I) (w : Fin 7 → Bool) :
    w ∈ P281Graphic.restrictedWords (l ∘ e) (r ∘ e)
      (fun i : {i // i ∉ Set.range e} => l i) (fun i : {i // i ∉ Set.range e} => r i) ↔
    (∑ j, enc (w j) • col l r (e j)) = 0 := by
  classical
  let v : I → Bit := ∑ j, enc (w j) • (Pi.single (e j) 1 : I → Bit)
  have hv (j : Fin 7) : v (e j) = enc (w j) := by
    dsimp only [v]; rw [Finset.sum_apply, Fintype.sum_eq_single j]
    · simp
    · intro i hi; simp [Pi.single_eq_of_ne (e.injective.ne hi.symm)]
  have hout (i : I) (hi : i ∉ Set.range e) : v i = 0 := by
    dsimp only [v]; rw [Finset.sum_apply]; apply Finset.sum_eq_zero
    intro j _; simp [Pi.single_eq_of_ne (show i ≠ e j from fun h => hi ⟨j,h.symm⟩)]
  have hq : (LinearMap.range (diffMap l r)).mkQ v = ∑ j, enc (w j) • col l r (e j) := by
    simp [v, col, map_sum]
  rw [← hq, ← LinearMap.mem_ker, Submodule.ker_mkQ]
  simp only [P281Graphic.restrictedWords, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨fun u => enc (x u), ?_⟩
    ext i
    by_cases hi : i ∈ Set.range e
    · obtain ⟨j,rfl⟩ := hi; rw [hv]
      change enc (x (r (e j))) - enc (x (l (e j))) = enc (decide (x (l (e j)) ≠ x (r (e j))))
      cases x (l (e j)) <;> cases x (r (e j)) <;> decide
    · rw [hout i hi]; change enc (x (r i)) - enc (x (l i)) = 0
      rw [hx ⟨i,hi⟩]; simp
  · rintro ⟨x,hx⟩
    refine ⟨fun u => dec (x u), ?_, ?_⟩
    · intro ⟨i,hi⟩; have h := congrFun hx i
      change x (r i) - x (l i) = v i at h
      rw [hout i hi, sub_eq_zero] at h; exact congrArg dec h.symm
    · ext j; have h := congrFun hx (e j)
      change x (r (e j)) - x (l (e j)) = v (e j) at h
      rw [hv] at h
      change decide (dec (x (l (e j))) ≠ dec (x (r (e j)))) = w j
      generalize x (l (e j)) = u at *; generalize x (r (e j)) = t at *
      generalize w j = b at h ⊢; revert h; cases b <;> fin_cases u <;> fin_cases t <;> decide

noncomputable section
variable {I V : Type} [Fintype I] [DecidableEq I]
theorem affineLabelsCard (l r : I → V) (s : Sig l r) (L : Submodule Bit (Sig l r))
    [Fintype L] (hs : s ∉ L) (hocc : ∀ x : L, x ≠ 0 → ∃ i, col l r i = s + (x : Sig l r)) :
    Fintype.card L ≤ 4 := by
  classical
  by_contra! hbig
  have hn : 3 ≤ Module.finrank Bit L := by
    rw [Module.card_eq_pow_finrank (K := Bit), ZMod.card] at hbig
    by_contra! h; have := Nat.pow_le_pow_right (n := 2) (by decide) (show Module.finrank Bit L ≤ 2 by omega); omega
  have hd : Module.finrank Bit Cube ≤ Module.finrank Bit L := by simpa [Cube] using hn
  obtain ⟨f,hf⟩ := finrank_le_iff_exists_linearMap.mp hd
  have hsel (j : Fin 7) := hocc (f (vec j)) (fun hz => fanoFacts.2.2.1 j (hf (hz.trans (map_zero f).symm)))
  choose idx hidx using hsel
  have hinj : Function.Injective idx := by
    intro i j hij; have h := (hidx i).symm.trans ((congrArg (col l r) hij).trans (hidx j))
    exact fanoFacts.2.2.2 i j (hf (Subtype.ext (add_left_cancel h)))
  let e : Fin 7 ↪ I := ⟨idx,hinj⟩
  let f' := L.subtype.comp f
  have hsum (w : Fin 7 → Bool) : (∑ j, enc (w j) • col l r (e j)) = par w • s + f' (syn w) := by
    simp only [e, Function.Embedding.coeFn_mk, hidx, smul_add, Finset.sum_add_distrib, par, syn, Finset.sum_smul, map_sum, map_smul, f', LinearMap.comp_apply, Submodule.subtype_apply]
  have hcode : P281Graphic.restrictedWords (l ∘ e) (r ∘ e)
      (fun i : {i // i ∉ Set.range e} => l i) (fun i : {i // i ∉ Set.range e} => r i) = code := by
    ext w; rw [cut_iff, hsum]; simp only [code, mem_filter, mem_univ, true_and, good]
    constructor
    · intro hz
      have hp : par w = 0 := by
        have hm : par w • s ∈ L := by
          have h := eq_neg_of_add_eq_zero_left hz
          rw [h]; exact L.neg_mem (f (syn w)).property
        generalize par w = z at *; fin_cases z
        · rfl
        · change (1 : Bit) • s ∈ L at hm; rw [one_smul] at hm; exact (hs hm).elim
      refine ⟨hp, hf ?_⟩
      rw [map_zero]; apply Subtype.ext; simpa [hp,f'] using hz
    · rintro ⟨hp,hy⟩; simp [hp,hy]
  apply P281Graphic.no_seven (l ∘ e) (r ∘ e)
      (fun i : {i // i ∉ Set.range e} => l i) (fun i : {i // i ∉ Set.range e} => r i) (by simp)
  · rw [hcode, fanoFacts.1]
  · rw [hcode]; intro w hw hn; exact fanoFacts.2.1 w (mem_filter.mp hw).2 hn
end
end PEqualNP.Outside.L_pcx_281_aux

namespace PEqualNP.Outside.L_pcx_281_aux

theorem orientCore {n m : ℕ} (left right : Fin m → Fin n) (sign : Fin m → Bool)
    (S : Finset (Fin m × Bool)) :
    let l := fun i : ↥S => left i.val.1
    let r := fun i : ↥S => right i.val.1
    let b := fun i : ↥S => sign i.val.1
    let faults := fun x : Fin n → Bool => S.filter (fun p => x (right p.1) ≠ (x (left p.1) ^^ sign p.1))
    let missed := fun x : Fin n → Bool => (faults x).filter (fun p => x (left p.1) = p.2)
    (∀ x, (missed x).Nonempty) → target l r b ≠ 0 ∧
      (∀ i, col l r i ≠ target l r b) ∧
      ∀ i j : ↥S, i ≠ j → col l r i + col l r j = target l r b →
        ∃ w, faults w = {i.val, j.val} ∧ missed w = {i.val} ∧ missed (fun v => !(w v)) = {j.val} := by
  classical
  intro l r b faults missed hm
  let flip := fun (x : Fin n → Bool) v => !(x v)
  have memF (x : Fin n → Bool) (i : ↥S) : i.val ∈ faults x ↔ x (r i) ≠ (x (l i) ^^ b i) := by
    simp [faults, i.property, l, r, b]
  have memM (x : Fin n → Bool) (p : Fin m × Bool) :
      p ∈ missed x ↔ p ∈ faults x ∧ x (left p.1) = p.2 := Finset.mem_filter
  have flipF (x : Fin n → Bool) : faults (flip x) = faults x := by
    ext p; simp [faults, flip]
  have excl (x : Fin n → Bool) (p : Fin m × Bool) (h : p ∈ missed x) : p ∉ missed (flip x) := by
    intro hf
    have h₁ := ((memM x p).mp h).2
    have h₂ := ((memM (flip x) p).mp hf).2
    simp [flip, h₁] at h₂
  have occ (x : Fin n → Bool) : ∃ i : ↥S, i.val ∈ missed x := by
    obtain ⟨p, hp⟩ := hm x
    exact ⟨⟨p, (Finset.mem_filter.mp ((memM x p).mp hp).1).1⟩, hp⟩
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    obtain ⟨x, hx⟩ := faultWord l r b 0 (by rw [map_zero, hz])
    obtain ⟨i, hi⟩ := occ x
    have := (hx i).mp ((memF x i).mp ((memM x _).mp hi).1)
    exact zero_ne_one this
  · intro i hi
    obtain ⟨x, hx⟩ := faultWord l r b (Pi.single i 1) hi
    have uniq (j : ↥S) (hj : j.val ∈ faults x) : j = i := by
      by_contra hne
      have := (hx j).mp ((memF x j).mp hj)
      simp [Pi.single_eq_of_ne hne] at this
    obtain ⟨u, hu⟩ := occ x
    obtain ⟨v, hv⟩ := occ (flip x)
    have h₁ := uniq u ((memM x _).mp hu).1
    have h₂ := uniq v (flipF x ▸ ((memM (flip x) _).mp hv).1)
    subst u; subst v
    exact excl _ _ hu hv
  · intro i j hij hc
    let y : ↥S → Bit := Pi.single i 1 + Pi.single j 1
    obtain ⟨x, hx⟩ := faultWord l r b y (by simpa only [y, map_add, col] using hc)
    have hf : faults x = {i.val, j.val} := by
      ext p
      by_cases hp : p ∈ S
      · let k : ↥S := ⟨p, hp⟩
        change k.val ∈ faults x ↔ k.val ∈ _
        rw [memF, hx]
        by_cases hki : k = i
        · subst i; simp [y, Pi.single_eq_of_ne hij]
        · by_cases hkj : k = j
          · subst j; simp [y, Pi.single_eq_of_ne hki]
          · have hpi : k.val ≠ i.val := fun h => hki (Subtype.ext h)
            have hpj : k.val ≠ j.val := fun h => hkj (Subtype.ext h)
            simp [y, Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj, hpi, hpj]
      · have hpi : p ≠ i.val := fun h => hp (h ▸ i.property)
        have hpj : p ≠ j.val := fun h => hp (h ▸ j.property)
        simp [faults, hp, hpi, hpj]
    obtain ⟨w, hw, hwi⟩ : ∃ w, faults w = {i.val, j.val} ∧ w (left i.val.1) = i.val.2 := by
      by_cases hx' : x (left i.val.1) = i.val.2
      · exact ⟨x, hf, hx'⟩
      · refine ⟨flip x, (flipF x).trans hf, ?_⟩
        change (!(x (left i.val.1))) = i.val.2
        cases h₁ : x (left i.val.1) <;> cases h₂ : i.val.2 <;> simp [h₁, h₂] at hx' ⊢
    have hi : i.val ∈ missed w := (memM _ _).mpr ⟨by simp [hw], hwi⟩
    have hchoice (p : Fin m × Bool) (hp : p ∈ missed (flip w)) : p = j.val := by
      have hf' := ((memM _ _).mp hp).1
      rw [flipF, hw] at hf'
      rcases Finset.mem_insert.mp hf' with rfl | hj
      · exact False.elim (excl w i.val hi hp)
      · exact Finset.mem_singleton.mp hj
    obtain ⟨q,hq⟩ := hm (flip w)
    have hj : j.val ∈ missed (flip w) := hchoice q hq ▸ hq
    refine ⟨w, hw, ?_, ?_⟩
    · ext p; rw [Finset.mem_singleton]; constructor
      · intro hp
        have hfp := ((memM _ _).mp hp).1
        rw [hw] at hfp
        rcases Finset.mem_insert.mp hfp with h | h
        · exact h
        · exact False.elim (excl w p hp (Finset.mem_singleton.mp h ▸ hj))
      · rintro rfl; exact hi
    · ext p; rw [Finset.mem_singleton]; exact ⟨hchoice p, fun h => h ▸ hj⟩

end PEqualNP.Outside.L_pcx_281_aux

namespace PEqualNP.Outside.L_pcx_281_aux
variable {A : Type} [DecidableEq A]

theorem liftPair (S : Finset A) {k : ℕ} (f : S → S)
    (hfix : (Finset.univ.filter fun i => f i = i).card ≤ k)
    (hinv : ∀ i, f (f i) = i) (P : A → A → Prop)
    (hP : ∀ i, f i ≠ i → P i (f i)) :
    ∃ F : A → A, (S.filter fun i => F i = i).card ≤ k ∧
      ∀ a ∈ S, F a ∈ S ∧ F (F a) = a ∧ (F a ≠ a → P a (F a)) := by
  classical
  let F (a : A) : A := if h : a ∈ S then (f ⟨a,h⟩).val else a
  have hF (i : S) : F i.val = (f i).val := dif_pos i.property
  refine ⟨F, ?_, ?_⟩
  · have he : (S.filter fun i => F i = i) = (Finset.univ.filter fun i => f i = i).map (Function.Embedding.subtype _) := by
      ext a
      simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.subtype_apply]
      constructor
      · rintro ⟨ha,h⟩; exact ⟨⟨a,ha⟩, Subtype.ext ((hF ⟨a,ha⟩).symm.trans h),rfl⟩
      · rintro ⟨i,hi,rfl⟩; exact ⟨i.property, (hF i).trans (congrArg Subtype.val hi)⟩
    simpa only [he,Finset.card_map] using hfix
  · intro a ha
    let i : S := ⟨a,ha⟩
    change F i.val ∈ S ∧ F (F i.val) = i.val ∧ _
    rw [hF i, hF (f i), hinv]
    refine ⟨(f i).property,rfl,?_⟩
    exact fun h => hP i (fun he => h (congrArg Subtype.val he))

theorem smallAttach (S : Finset A) (g : ℕ) {X : Type} (ok : X → A → Prop)
    (h : ∀ T : Finset A, T.card < g → ∃ x, ∀ a ∈ T, ok x a) :
    ∀ T : Finset S, T.card < g → ∃ x, ∀ i ∈ T, ok x i.val := by
  intro T ht
  obtain ⟨x,hx⟩ := h (T.map (Function.Embedding.subtype _)) (by simpa only [Finset.card_map] using ht)
  exact ⟨x,fun i hi => hx i.val (Finset.mem_map.mpr ⟨i,hi,rfl⟩)⟩
end PEqualNP.Outside.L_pcx_281_aux

namespace PEqualNP.Outside.L_pcx_281_aux
namespace P281Walsh
open scoped BigOperators
abbrev F := ZMod 2
variable {Q I : Type*} [AddCommGroup Q] [Module F Q] [Finite Q] [Fintype I]

noncomputable def flag (p : Prop) : ℤ := by classical exact if p then 1 else 0
noncomputable def mult (c : I → Q) (q : Q) : ℕ := by
  classical exact (Finset.univ.filter (fun i => c i = q)).card

private abbrev Odd (s : Q) := {h : Q →ₗ[F] F // h s = 1}
private noncomputable local instance (s : Q) : Fintype (Odd s) := by
  letI : Finite (Q →ₗ[F] F) := Finite.of_injective (fun h => (h : Q → F)) DFunLike.coe_injective
  exact Fintype.ofFinite _
private def sign (b : F) : ℤ := if b = 0 then 1 else -1
private lemma binary (a : F) : a = 0 ∨ a = 1 := by revert a; decide
private lemma sign_add (a b : F) : sign (a+b) = sign a * sign b := by revert a b; decide
private lemma flip (a : F) : a+1 = 0 ↔ a = 1 := by revert a; decide
omit [Finite Q] in
private lemma switch (a b s : Q) : a+b=s ↔ a=b+s := by
  constructor <;> intro h
  · have := congrArg (·+b) h; simpa [add_assoc, ZModModule.add_self, add_comm s b] using this
  · rw [h]; simp [add_comm b s, add_assoc, ZModModule.add_self]

private lemma orth (s q : Q) (hs : s ≠ 0) :
    (∑ h : Odd s, sign (h.1 q)) = (Fintype.card (Odd s) : ℤ) * (flag (q=0) - flag (q=s)) := by
  classical
  by_cases h0 : q=0
  · subst q; simp [sign,flag,hs.symm]
  by_cases h1 : q=s
  · subst q
    have e (h : Odd s) : h.1 s = 1 := h.2
    simp [e,sign,flag,hs]
  have hn : q ∉ Submodule.span F {s} := by
    rintro h; obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp h
    rcases binary a with rfl|rfl <;> simp_all
  obtain ⟨k,hk,hker⟩ := Submodule.exists_le_ker_of_notMem hn
  have hks : k s = 0 := hker (Submodule.subset_span (by simp))
  have hkq : k q = 1 := (binary _).resolve_left hk
  let t : Odd s → Odd s := fun h => ⟨h.1+k, by simp [hks,h.2]⟩
  have ht : Function.Involutive t := fun h => by
    apply Subtype.ext; change (h.1+k)+k=h.1; simp [add_assoc,ZModModule.add_self]
  let e := ht.toPerm t
  have hneg : ∀ h : Odd s, sign ((e h).1 q) = -sign (h.1 q) := by
    intro h; change sign ((h.1+k) q) = _
    rw [LinearMap.add_apply, hkq, sign_add]; simp [sign]
  have he := Equiv.sum_comp e (fun h : Odd s => sign (h.1 q))
  simp_rw [hneg, Finset.sum_neg_distrib] at he
  simp [flag,h0,h1]; omega

private def slack (s : Q) (c : I → Q) (h : Odd s) : ℤ := 1 - ∑ i, sign (h.1 (c i))
omit [Finite Q] in
private lemma slack_lower (s : Q) (c : I → Q) (g : ℕ)
    (hw : ∀ h : Q →ₗ[F] F, h s=1 → g ≤ (Finset.univ.filter (fun i => h (c i)=1)).card)
    (h : Odd s) : 1 + 2*(g : ℤ) - Fintype.card I ≤ slack s c h := by
  classical
  have hb (a : F) : sign a = 1-2*(if a=1 then 1 else 0 : ℤ) := by revert a; decide
  simp only [slack,hb,Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_boole,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  have := hw h.1 h.2
  omega

private lemma walsh (s : Q) (hs : s≠0) (c : I → Q) (q : Q) :
    (∑ h : Odd s, slack s c h * sign (h.1 q)) = (Fintype.card (Odd s) : ℤ) *
    (flag (q=0)-flag (q=s)-(mult c q : ℤ)+mult c (q+s)) := by
  classical
  have hh (h : Odd s) : slack s c h * sign (h.1 q) = sign (h.1 q) - ∑ i, sign (h.1 (c i + q)) := by
    simp [slack,sub_mul,Finset.sum_mul,sign_add]
  simp_rw [hh]; rw [Finset.sum_sub_distrib, Finset.sum_comm]; simp_rw [orth s _ hs]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  have hc (a : Q) : (∑ i, flag (c i=a)) = (mult c a : ℤ) := by
    simp only [mult,flag,Finset.sum_boole]
  simp only [switch,add_zero,hc]; ring

private lemma saturate {A : Type*} [Fintype A] (w : A → ℤ) (b : A → F) (z : ℤ)
    (hw : ∀ a, 0 ≤ w a) (hm : 0 < ∑ a,w a)
    (hz : (∑ a,w a) * z = ∑ a,w a * sign (b a)) :
    z = flag (∀ a, 0 < w a → b a=0) - flag (∀ a, 0 < w a → b a=1) := by
  classical
  have hlo (a : A) : -w a ≤ w a * sign (b a) := by
    rcases binary (b a) with h|h <;> simp [sign,h]
    linarith [hw a]
  have hhi (a : A) : w a * sign (b a) ≤ w a := by
    rcases binary (b a) with h|h <;> simp [sign,h]
    linarith [hw a]
  have ha : ∃ a, 0 < w a := by
    by_contra! hh; have he (a : A) : w a = 0 := le_antisymm (hh a) (hw a)
    simp [he] at hm
  obtain ⟨a,ha⟩ := ha
  by_cases h0 : ∀ a, 0 < w a → b a=0
  · have h1 : ¬∀ a, 0 < w a → b a=1 := fun h => zero_ne_one ((h0 a ha).symm.trans (h a ha))
    have e (j : A) : w j * sign (b j) = w j := by
      by_cases hj : 0 < w j
      · simp [h0 j hj,sign]
      · have := hw j; have : w j=0 := by omega
        simp [this]
    simp only [e] at hz
    simp only [flag,ite_eq_left h0,ite_eq_right h1,sub_zero]
    exact mul_left_cancel₀ hm.ne' (hz.trans (mul_one _).symm)
  by_cases h1 : ∀ a, 0 < w a → b a=1
  · have e (j : A) : w j * sign (b j) = -w j := by
      by_cases hj : 0 < w j
      · simp [h1 j hj,sign]
      · have := hw j; have : w j=0 := by omega
        simp [this]
    simp only [e,Finset.sum_neg_distrib] at hz
    simp only [flag,ite_eq_right h0,ite_eq_left h1,zero_sub]
    exact mul_left_cancel₀ hm.ne' (hz.trans (mul_neg_one _).symm)
  simp only [flag,ite_eq_right h0,ite_eq_right h1,sub_zero]
  push Not at h0 h1
  obtain ⟨j,hj,hb⟩ := h0
  obtain ⟨k,hk,hc⟩ := h1
  have hi := Finset.sum_lt_sum (s:=Finset.univ) (fun i _ => hhi i)
    ⟨j,Finset.mem_univ _,by simp [sign,hb]; omega⟩
  have lo := Finset.sum_lt_sum (s:=Finset.univ) (fun i _ => hlo i)
    ⟨k,Finset.mem_univ _,by simp [sign,(binary _).resolve_right hc]; omega⟩
  rw [← hz] at hi
  rw [Finset.sum_neg_distrib,← hz] at lo
  have hu : z < 1 := (lt_of_mul_lt_mul_left (by simpa using hi : (∑ a,w a)*z < (∑ a,w a)*1) hm.le)
  have hl : -1 < z := (lt_of_mul_lt_mul_left (by simpa using lo : (∑ a,w a)*(-1) < (∑ a,w a)*z) hm.le)
  omega

private lemma chart_pos (s : Q) (hs : s ≠ 0) : 0 < (Fintype.card (Odd s) : ℤ) := by
  obtain ⟨h,hh⟩ := Module.Projective.exists_dual_eq_one F hs
  have : Nonempty (Odd s) := ⟨⟨h,hh⟩⟩
  exact_mod_cast (Fintype.card_pos (α := Odd s))

private lemma total (s : Q) (hs : s ≠ 0) (c : I → Q) (hc : ∀ i, c i ≠ s) :
    ∑ a,slack s c a = (Fintype.card (Odd s) : ℤ) * (1-(mult c 0 : ℤ)) := by
  have hcs : mult c s = 0 := by classical simp [mult,hc]
  simpa [flag,sign,hs.symm,hcs] using walsh s hs c 0

theorem bound_balance (s : Q) (c : I → Q) (g : ℕ) (hs : s ≠ 0) (hc : ∀ i, c i ≠ s)
    (hw : ∀ h : Q →ₗ[F] F, h s=1 → g ≤ (Finset.univ.filter (fun i => h (c i)=1)).card) :
    2*g ≤ Fintype.card I ∧ (Fintype.card I=2*g → ∀ q, mult c q=mult c (q+s)) := by
  classical
  let M : ℤ := Fintype.card (Odd s)
  have pos : 0 < M := chart_pos s hs
  have avg := Finset.sum_le_sum (s:=Finset.univ) (fun a _ => slack_lower s c g hw a)
  rw [total s hs c hc] at avg
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at avg
  change M * _ ≤ M * _ at avg
  have le := (mul_le_mul_iff_right₀ pos).mp avg
  constructor
  · omega
  intro ht q
  have hz : mult c 0=0 := by omega
  have nn (h : Odd s) : 0 ≤ slack s c h - 1 := by have := slack_lower s c g hw h; omega
  have sm : ∑ h : Odd s, (slack s c h - 1) = 0 := by
    rw [Finset.sum_sub_distrib,total s hs c hc]; simp [hz]
  have he (h : Odd s) : slack s c h=1 := by
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => nn a)).mp sm h (Finset.mem_univ _)
    omega
  have eqn := walsh s hs c q
  simp only [he,one_mul,orth s q hs] at eqn
  have := mul_left_cancel₀ pos.ne' eqn
  omega

theorem classify (s : Q) (c : I → Q) (g : ℕ) (hs : s ≠ 0) (hc : ∀ i, c i ≠ s)
    (hn : Fintype.card I ≤ 2*g+1)
    (hw : ∀ h : Q →ₗ[F] F, h s=1 → g ≤ (Finset.univ.filter (fun i => h (c i)=1)).card) :
    (mult c 0 = 1 ∧ ∀ q, q≠0 → q≠s → mult c q = mult c (q+s)) ∨
    (mult c 0 = 0 ∧ ∃ L : Submodule F Q, s ∉ L ∧ ∀ q, q≠0 → q≠s →
      (mult c q : ℤ) - mult c (q+s) = flag (q+s ∈ L) - flag (q ∈ L)) := by
  classical
  let M : ℤ := Fintype.card (Odd s)
  have hM : 0 < M := chart_pos s hs
  let w := slack s c
  have hw' (h : Odd s) : 0 ≤ w h := by have := slack_lower s c g hw h; dsimp [w]; omega
  have mass : ∑ a,w a = M * (1-(mult c 0 : ℤ)) := total s hs c hc
  have nn : 0 ≤ ∑ a,w a := Finset.sum_nonneg (fun a _ => hw' a)
  have one : mult c 0 ≤ 1 := by
    by_contra! hh
    have : 1 - (mult c 0 : ℤ) < 0 := by omega
    linarith [mul_neg_of_pos_of_neg hM this]
  have spec (q : Q) (h0 : q≠0) (h1 : q≠s) :
      M * (-(mult c q : ℤ) + mult c (q+s)) = ∑ a,w a * sign (a.1 q) := by
    simpa [w,M,flag,h0,h1] using (walsh s hs c q).symm
  by_cases hz : mult c 0 = 1
  · left; refine ⟨hz,fun q h0 h1 => ?_⟩
    have hm : ∑ a,w a = 0 := by simp [mass,hz]
    have he (a : Odd s) : w a=0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hw' a)).mp hm a (Finset.mem_univ _)
    have hq := spec q h0 h1
    simp [he,hM.ne'] at hq
    omega
  right
  have hz' : mult c 0 = 0 := by omega
  have hm : ∑ a,w a = M := by simp [mass,hz']
  let L : Submodule F Q := ⨅ a : {a : Odd s // 0 < w a}, a.1.1.ker
  have mem (q : Q) : q∈L ↔ ∀ a : Odd s, 0 < w a → a.1 q = 0 := by
    simp [L,Submodule.mem_iInf,LinearMap.mem_ker,Subtype.forall]
  have sn : s ∉ L := by
    intro hs'
    have he (a : Odd s) : w a=0 := by
      by_contra! h
      have ha := (mem s).mp hs' a (lt_of_le_of_ne (hw' a) h.symm)
      rw [a.2] at ha; exact one_ne_zero ha
    simp [he] at hm; omega
  refine ⟨hz',L,sn,fun q h0 h1 => ?_⟩
  have mem' : q+s∈L ↔ ∀ a : Odd s, 0 < w a → a.1 q = 1 := by
    have ev (a : Odd s) : a.1 s=1 := a.2
    rw [mem]; simp only [map_add,ev,flip]
  have eqn := saturate w (fun a : Odd s => a.1 q) (-(mult c q : ℤ)+mult c (q+s))
    hw' (hm.trans_gt hM) (by rw [hm]; exact spec q h0 h1)
  rw [← propext (mem q),← propext mem'] at eqn
  omega

end P281Walsh
end PEqualNP.Outside.L_pcx_281_aux

namespace PEqualNP.Outside.L_pcx_281_aux
namespace P281Match

private theorem countInsert {I Q : Type*} [DecidableEq I] [DecidableEq Q]
    (c : I → Q) (q : Q) (i : I) (S : Finset I) (hi : i ∉ S) :
    ((insert i S).filter (fun x => c x = q)).card =
      (S.filter (fun x => c x = q)).card + (if c i = q then 1 else 0) := by
  by_cases h : c i = q <;> simp [Finset.filter_insert, h, hi]

theorem pairLabels {I Q : Type*} [DecidableEq I] [Fintype Q] [DecidableEq Q]
    (c : I → Q) (t : Q → Q) (ht : Function.Involutive t) (hn : ∀ q, t q ≠ q)
    (S : Finset I) :
    ∃ M : I → I,
      (∀ i ∈ S, M i ∈ S ∧ M (M i) = i ∧ (M i ≠ i → c (M i) = t (c i))) ∧
      (S.filter (fun i => M i = i)).card = ∑ q : Q,
        ((S.filter (fun i => c i = q)).card - (S.filter (fun i => c i = t q)).card) := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hpair : ∃ a ∈ S, ∃ b ∈ S, c b = t (c a)
    · obtain ⟨a, ha, b, hb, hcb⟩ := hpair
      have hab : a ≠ b := by rintro rfl; exact hn _ hcb.symm
      have hba := Ne.symm hab
      let R := (S.erase a).erase b
      have hRS : R ⊂ S := Finset.ssubset_of_subset_of_ssubset (Finset.erase_subset ..)
        (Finset.erase_ssubset ha)
      obtain ⟨M, hM, hcard⟩ := ih R hRS
      let N := fun i => if i = a then b else if i = b then a else M i
      have hNa : N a = b := by simp [N]
      have hNb : N b = a := by simp [N, hba]
      have hNR : ∀ i ∈ R, N i = M i := by
        intro i hi
        simp only [R, Finset.mem_erase] at hi
        simp [N, hi.1, hi.2.1]
      have hS : S = insert a (insert b R) := by
        ext i
        simp only [Finset.mem_insert, R, Finset.mem_erase]
        grind
      refine ⟨N, ?_, ?_⟩
      · intro i hi
        by_cases hia : i = a
        · subst i; exact ⟨hNa ▸ hb, by rw [hNa,hNb], fun _ => hNa ▸ hcb⟩
        by_cases hib : i = b
        · subst i
          refine ⟨hNb ▸ ha, by rw [hNb,hNa], fun _ => ?_⟩
          rw [hNb, hcb, ht]
        have hir : i ∈ R := by simp [R, hia, hib, hi]
        obtain ⟨hmr, hmi, hmc⟩ := hM i hir
        rw [hNR i hir, hNR (M i) hmr]
        exact ⟨hRS.subset hmr, hmi, hmc⟩
      · have hfixed : S.filter (fun i => N i = i) = R.filter (fun i => M i = i) := by
          ext i
          by_cases hia : i = a
          · subst i; simp [R, hNa, hba]
          by_cases hib : i = b
          · subst i; simp [R, hNb, hab]
          simp [R, N, hia, hib]
        rw [hfixed, hcard]
        apply Finset.sum_congr rfl
        intro q _
        have har : a ∉ insert b R := by simp [R, hab]
        have hbr : b ∉ R := by simp [R]
        have h1 : (c a = t q) ↔ (c b = q) := by
          rw [hcb]
          constructor
          · intro h; rw [h, ht]
          · intro h; rw [← h, ht]
        have h2 : (c b = t q) ↔ (c a = q) := by rw [hcb, ht.injective.eq_iff]
        conv_rhs => rw [hS, countInsert c q a _ har, countInsert c (t q) a _ har,
          countInsert c q b _ hbr, countInsert c (t q) b _ hbr]
        simp only [h1, h2]
        split_ifs <;> omega
    · refine ⟨id, fun i hi => ⟨hi, rfl, fun hn => (hn rfl).elim⟩, ?_⟩
      simp only [id_eq, Finset.filter_true]
      calc
        S.card = ∑ q : Q, (S.filter (fun i => c i = q)).card :=
          Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
        _ = _ := by
          apply Finset.sum_congr rfl
          intro q _
          by_cases hex : (S.filter (fun i => c i = q)).Nonempty
          · obtain ⟨a, ha⟩ := hex
            obtain ⟨haS, har⟩ := Finset.mem_filter.mp ha
            have hz : S.filter (fun i => c i = t q) = ∅ := by
              apply Finset.filter_false_of_mem
              intro b hb h
              exact hpair ⟨a, haS, b, hb, har ▸ h⟩
            simp [hz]
          · simp [Finset.not_nonempty_iff_eq_empty.mp hex]

end P281Match
end PEqualNP.Outside.L_pcx_281_aux

namespace PEqualNP.Outside.L_pcx_281_aux
namespace P281Match
open P281Walsh (mult flag)
open scoped BigOperators
variable {I Q : Type*} [Fintype I] [DecidableEq I] [AddCommGroup Q] [Module (ZMod 2) Q] [Finite Q]

omit [Finite Q] in
private lemma flip_invol (s : Q) : Function.Involutive (fun q : Q => q+s) := by
  intro q; simp [add_assoc, ZModModule.add_self]

omit [Finite Q] in
private lemma byCounts (s : Q) (c : I → Q) (hs : s ≠ 0) [Fintype Q] :
    ∃ f : I → I, (Finset.univ.filter (fun i => f i=i)).card =
      ∑ q : Q, (mult c q - mult c (q+s)) ∧ Function.Involutive f ∧
      ∀ i, f i ≠ i → c i + c (f i) = s := by
  classical
  obtain ⟨f,hf,hcount⟩ := pairLabels c (fun q => q+s) (flip_invol s)
    (fun q h => hs (add_eq_left.mp h)) Finset.univ
  refine ⟨f, hcount, fun i => (hf i (Finset.mem_univ _)).2.1, ?_⟩
  intro i hi
  rw [(hf i (Finset.mem_univ _)).2.2 hi, ← add_assoc, ZModModule.add_self, zero_add]

theorem fixedZero (s : Q) (c : I → Q) (hs : s ≠ 0)
    (h : ∀ q, mult c q = mult c (q+s)) :
    ∃ f : I → I, (Finset.univ.filter (fun i => f i=i)).card = 0 ∧
      Function.Involutive f ∧ ∀ i, f i ≠ i → c i + c (f i) = s := by
  classical
  let := Fintype.ofFinite Q
  obtain ⟨f,hf,hm⟩ := byCounts s c hs
  refine ⟨f, hf.trans ?_, hm⟩
  exact Finset.sum_eq_zero fun q _ => Nat.sub_eq_zero_of_le (h q).le

theorem fixedThree (s : Q) (c : I → Q) (hs : s ≠ 0) (hc : ∀ i, c i ≠ s)
    (H : (mult c 0 = 1 ∧ ∀ q, q≠0 → q≠s → mult c q = mult c (q+s)) ∨
      (mult c 0 = 0 ∧ ∃ L : Submodule (ZMod 2) Q, s ∉ L ∧ ∀ q, q≠0 → q≠s →
        (mult c q : ℤ) - mult c (q+s) = flag (q+s ∈ L) - flag (q ∈ L)))
    (hL : ∀ (L : Submodule (ZMod 2) Q) [Fintype L], s ∉ L →
      (∀ x : L, x ≠ 0 → ∃ i, c i = s + (x : Q)) → Fintype.card L ≤ 4) :
    ∃ f : I → I, (Finset.univ.filter (fun i => f i=i)).card ≤ 3 ∧
      Function.Involutive f ∧ ∀ i, f i ≠ i → c i + c (f i) = s := by
  classical
  let := Fintype.ofFinite Q
  obtain ⟨f,hcount,hm⟩ := byCounts s c hs
  refine ⟨f, ?_, hm⟩
  rw [hcount]
  have hms : mult c s = 0 := by
    simp [mult, Finset.filter_false_of_mem (fun i (_ : i ∈ (Finset.univ : Finset I)) => hc i)]
  rcases H with ⟨hzero,hbal⟩ | ⟨hzero,L,hLs,hbal⟩
  · calc
      _ ≤ ∑ q : Q, (if q = 0 then 1 else 0 : ℕ) := by
        apply Finset.sum_le_sum
        intro q _
        by_cases hq : q=0
        · subst q; simp [hzero,hms]
        by_cases he : q=s
        · subst q; simp [hms,hs]
        simp [hq, Nat.sub_eq_zero_of_le (hbal q hq he).le]
      _ ≤ 3 := by simp
  · let : Fintype L := Fintype.ofFinite L
    have hout (x : Q) (hx : x ∈ L) : x+s ∉ L := by
      intro h
      exact hLs (by simpa [← add_assoc, ZModModule.add_self] using L.add_mem hx h)
    have hsize := hL L hLs (by
      intro x hx
      have hx0 : (x:Q) ≠ 0 := fun he => hx (Subtype.ext he)
      have hxs : (x:Q) ≠ s := fun he => hLs (he ▸ x.property)
      have hval := hbal (x:Q) hx0 hxs
      simp only [flag, hout x x.property, x.property, ite_false, ite_true] at hval
      have hp : 0 < mult c ((x:Q)+s) := by omega
      obtain ⟨i,hi⟩ := Finset.card_pos.mp hp
      exact ⟨i, by simpa [add_comm s] using (Finset.mem_filter.mp hi).2⟩)
    let A := (Finset.univ.filter (fun q : Q => q ∈ L)).erase 0
    have hcardA : A.card = Fintype.card L - 1 := by
      calc
        A.card = (Finset.univ.filter (fun q : Q => q ∈ L)).card - 1 :=
          Finset.card_erase_of_mem (by simp)
        _ = _ := by rw [Fintype.card_subtype (fun q : Q => q ∈ L)]
    calc
      _ ≤ ∑ q : Q, (if q+s ∈ A then 1 else 0 : ℕ) := by
        apply Finset.sum_le_sum
        intro q _
        by_cases hq : q=0
        · subst q; simp [hzero]
        by_cases he : q=s
        · subst q; simp [hms]
        have hnon : q+s ≠ 0 := by
          intro e
          apply he
          simpa [add_assoc, ZModModule.add_self] using congrArg (·+s) e
        have hval := hbal q hq he
        by_cases hqL : q ∈ L <;> by_cases ha : q+s ∈ L <;>
          simp [flag,A,hqL,ha,hnon] at hval ⊢ <;> omega
      _ = ∑ q : Q, (if q ∈ A then 1 else 0 : ℕ) :=
        (flip_invol s).bijective.sum_comp (fun q => if q ∈ A then 1 else 0)
      _ = A.card := by simp
      _ ≤ 3 := by omega

theorem fromWalsh (s : Q) (c : I → Q) (g : ℕ) (hs : s ≠ 0) (hc : ∀ i, c i ≠ s)
    (hn : Fintype.card I ≤ 2*g+1)
    (hw : ∀ h : Q →ₗ[ZMod 2] ZMod 2, h s=1 →
      g ≤ (Finset.univ.filter (fun i => h (c i)=1)).card)
    (hL : ∀ (L : Submodule (ZMod 2) Q) [Fintype L], s ∉ L →
      (∀ x : L, x≠0 → ∃ i, c i=s+(x:Q)) → Fintype.card L ≤ 4) :
    2*g ≤ Fintype.card I ∧ ∃ f : I → I,
      (Finset.univ.filter (fun i => f i=i)).card ≤ (if Fintype.card I=2*g then 0 else 3) ∧
      (∀ i, f (f i)=i) ∧ ∀ i, f i≠i → c i + c (f i)=s := by
  obtain ⟨hlo,hbal⟩ := P281Walsh.bound_balance s c g hs hc hw
  refine ⟨hlo, ?_⟩
  by_cases heq : Fintype.card I = 2*g
  · obtain ⟨f,hf,hm⟩ := fixedZero s c hs (hbal heq)
    exact ⟨f, by simp [hf,heq], hm⟩
  · obtain ⟨f,hf,hm⟩ := fixedThree s c hs hc (P281Walsh.classify s c g hs hc hn hw) hL
    exact ⟨f, by simpa [heq] using hf, hm⟩

end P281Match
end PEqualNP.Outside.L_pcx_281_aux

open PEqualNP.Outside.L_pcx_281_aux in
theorem PEqualNP.Outside.L_pcx_281 : (∀ (n m : ℕ) (left right : Fin m → Fin n) (sign : Fin m → Bool),
  let cl := fun p : Fin m × Bool =>
    ({(left p.1,!p.2), (right p.1, p.2 ^^ sign p.1)} : PEqualNP.ProofComplexity.Clause (Fin n))
  let F : Set (PEqualNP.ProofComplexity.Clause (Fin n)) := Set.range cl
  let negative := fun k : ℕ => ∃ (v : ℕ → Fin n) (edge : ℕ → Fin m),
    v 0 = v k ∧ Odd (((Finset.range k).filter (fun j => sign (edge j) = true)).card) ∧
    ∀ j < k, (v j = left (edge j) ∧ v (j+1) = right (edge j)) ∨
      (v j = right (edge j) ∧ v (j+1) = left (edge j))
  ∀ g : ℕ, negative g → (∀ k < g, ¬ negative k) →
    ∀ π, PEqualNP.ProofComplexity.IsRefutation F π → π.length ≤ 4*g+1 →
    ∃ S : Finset (Fin m × Bool), Set.InjOn cl (S : Set (Fin m × Bool)) ∧
      (∀ p ∈ S, cl p ∈ π) ∧ 2*g ≤ S.card ∧ 2*S.card ≤ π.length+1 ∧
      let faults := fun x : Fin n → Bool => S.filter
        (fun p => x (right p.1) ≠ (x (left p.1) ^^ sign p.1))
      let missed := fun y : Fin n → Bool =>
        (faults y).filter (fun p => y (left p.1) = p.2)
      (∀ x, (missed x).Nonempty) ∧
      ∃ mate : (Fin m × Bool) → (Fin m × Bool),
        (S.filter (fun p => mate p = p)).card ≤ (if S.card = 2*g then 0 else 3) ∧
        ∀ p ∈ S, mate p ∈ S ∧ mate (mate p) = p ∧
          (mate p ≠ p → ∃ word, faults word = {p, mate p} ∧ missed word = {p} ∧
            missed (fun v => !(word v)) = {mate p})) := by
  classical
  intro n m left right sign cl F negative g _ hmin π href hlen
  obtain ⟨S, hinj, hocc, hsize, hmiss⟩ := extractCore left right sign href
  let l := fun i : ↥S => left i.val.1
  let r := fun i : ↥S => right i.val.1
  let b := fun i : ↥S => sign i.val.1
  let s := target l r b
  let c := col l r
  letI : Fintype (Sig l r) := Fintype.ofFinite _
  obtain ⟨hs, hc, hpairs⟩ := orientCore left right sign S hmiss
  have hn : Fintype.card ↥S ≤ 2*g+1 := by rw [Fintype.card_coe]; omega
  have hsmall := smallAttach S g (fun (x : Fin n → Bool) (p : Fin m × Bool) => x (right p.1) = (x (left p.1) ^^ sign p.1)) (small_consistent left right sign hmin)
  have hw := oddRowLarge l r b hsmall
  obtain ⟨hlow,f,hfix,hinv,hlabel⟩ := P281Match.fromWalsh s c g hs hc hn hw (affineLabelsCard l r s)
  rw [Fintype.card_coe] at hlow hfix
  refine ⟨S, hinj, hocc, hlow, hsize, hmiss, ?_⟩
  let faults := fun x : Fin n → Bool => S.filter (fun p => x (right p.1) ≠ (x (left p.1) ^^ sign p.1))
  let missed := fun x : Fin n → Bool => (faults x).filter (fun p => x (left p.1) = p.2)
  apply liftPair S f hfix hinv (fun i j => ∃ w, faults w = {i,j} ∧ missed w = {i} ∧ missed (fun v => !(w v)) = {j})
  intro i hi
  exact hpairs i (f i) (Ne.symm hi) (hlabel i hi)
