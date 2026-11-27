import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_327_aux

open PEqualNP.ProofComplexity

abbrev RawT (n b : ℕ) : Type := (_ : Fin n) × Fin b
abbrev RVec (n b : ℕ) : Type := Fin n → Fin (b - 1) → Bool
abbrev Part (n b : ℕ) : Type := RawT n b → Option Bool

def parityFn {n b : ℕ} (y : RawT n b → Bool) (i : Fin n) : Bool :=
  decide (Odd ((Finset.univ : Finset (Fin b)).filter (fun j => y ⟨i, j⟩ = true)).card)

def fixedIn {n b : ℕ} (ρ : Part n b) (i : Fin n) : Finset (Fin b) :=
  Finset.univ.filter (fun j => (ρ ⟨i, j⟩).isSome)

def onesIn {n b : ℕ} (ρ : Part n b) (i : Fin n) : Finset (Fin b) :=
  Finset.univ.filter (fun j => ρ ⟨i, j⟩ = some true)

def fullBlocks {n b : ℕ} (ρ : Part n b) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ∀ j : Fin b, (ρ ⟨i, j⟩).isSome)

def agrees {n b : ℕ} (y : RawT n b → Bool) (ρ : Part n b) : Prop :=
  ∀ u bit, ρ u = some bit → y u = bit

def stepBit {n b : ℕ} (v : List Bool → RawT n b) (r : RVec n b) (x : Fin n → Bool)
    (q : List Bool) (ρ : Part n b) : Bool :=
  match ρ (v q) with
  | some bit => bit
  | none =>
    let i := (v q).1
    let c := (fixedIn ρ i).card
    if h : c < b - 1 then
      r i ⟨c, h⟩
    else
      decide (Odd (onesIn ρ i).card) != x i

def stepRho {n b : ℕ} (v : List Bool → RawT n b)
    (q : List Bool) (bit : Bool) (ρ : Part n b) : Part n b :=
  match ρ (v q) with
  | some _ => ρ
  | none => Function.update ρ (v q) (some bit)

def pathRhoAux {n b : ℕ} (v : List Bool → RawT n b)
    (ρ : Part n b) (pref : List Bool) : List Bool → Part n b
  | [] => ρ
  | bit :: rest => pathRhoAux v (stepRho v pref bit ρ) (pref ++ [bit]) rest

def pathRho {n b : ℕ} (v : List Bool → RawT n b) (p : List Bool) : Part n b :=
  pathRhoAux v (fun _ => none) [] p

lemma pathRhoAux_append_singleton {n b : ℕ} (v : List Bool → RawT n b)
    (ρ : Part n b) (pref p : List Bool) (bit : Bool) :
    pathRhoAux v ρ pref (p ++ [bit]) = stepRho v (pref ++ p) bit (pathRhoAux v ρ pref p) := by
  induction p generalizing ρ pref with
  | nil => simp [pathRhoAux]
  | cons a rest ih =>
    simp only [List.cons_append, pathRhoAux]
    rw [ih, List.append_assoc, List.singleton_append]

lemma pathRho_append_singleton {n b : ℕ} (v : List Bool → RawT n b)
    (p : List Bool) (bit : Bool) :
    pathRho v (p ++ [bit]) = stepRho v p bit (pathRho v p) := by
  simpa [pathRho] using pathRhoAux_append_singleton v (fun _ => none) [] p bit

lemma stepRho_of_some {n b : ℕ} (v : List Bool → RawT n b) (q : List Bool) (bit : Bool)
    (ρ : Part n b) {u : RawT n b} {c : Bool} (h : ρ u = some c) :
    stepRho v q bit ρ u = some c := by
  unfold stepRho
  cases hq : ρ (v q) with
  | some _ => exact h
  | none =>
    by_cases hu : u = v q
    · subst hu; rw [hq] at h; cases h
    · simp [Function.update_of_ne hu, h]

lemma stepRho_isSome {n b : ℕ} (v : List Bool → RawT n b) (q : List Bool) (bit : Bool)
    (ρ : Part n b) {u : RawT n b} (h : (ρ u).isSome) :
    (stepRho v q bit ρ u).isSome := by
  cases hc : ρ u with
  | none => simp [hc] at h
  | some c => rw [stepRho_of_some v q bit ρ hc]; rfl

lemma stepRho_ne {n b : ℕ} (v : List Bool → RawT n b) (q : List Bool) (bit : Bool)
    (ρ : Part n b) {u : RawT n b} (hu : u ≠ v q) :
    stepRho v q bit ρ u = ρ u := by
  unfold stepRho
  cases ρ (v q) with
  | some _ => rfl
  | none => simp [Function.update_of_ne hu]

lemma pathRho_take_mono {n b : ℕ} (v : List Bool → RawT n b) (p : List Bool)
    {t₁ t₂ : ℕ} (ht : t₁ ≤ t₂) {u : RawT n b} {c : Bool}
    (h : pathRho v (p.take t₁) u = some c) :
    pathRho v (p.take t₂) u = some c := by
  induction ht with
  | refl => exact h
  | @step m htm ih =>
    by_cases hm : m < p.length
    · rw [List.take_succ_eq_append_getElem hm, pathRho_append_singleton]
      exact stepRho_of_some v _ _ _ ih
    · have h1 : p.take (m + 1) = p := List.take_of_length_le (by omega)
      have h2 : p.take m = p := List.take_of_length_le (by omega)
      rw [h1, ← h2]; exact ih

lemma fullBlocks_take_mono {n b : ℕ} (v : List Bool → RawT n b) (p : List Bool)
    {t₁ t₂ : ℕ} (ht : t₁ ≤ t₂) :
    fullBlocks (pathRho v (p.take t₁)) ⊆ fullBlocks (pathRho v (p.take t₂)) := by
  intro i hi
  simp only [fullBlocks, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  intro j
  cases hc : pathRho v (p.take t₁) ⟨i, j⟩ with
  | none => have := hi j; simp [hc] at this
  | some c => rw [pathRho_take_mono v p ht hc]; rfl

lemma fixedIn_card_eq_iff {n b : ℕ} (ρ : Part n b) (i : Fin n) :
    (fixedIn ρ i).card = b ↔ i ∈ fullBlocks ρ := by
  have h : (fixedIn ρ i).card = (Finset.univ : Finset (Fin b)).card ↔ fixedIn ρ i = Finset.univ :=
    Finset.card_eq_iff_eq_univ _
  simp only [Finset.card_univ, Fintype.card_fin] at h
  rw [h]
  simp only [fixedIn, fullBlocks, Finset.eq_univ_iff_forall, Finset.mem_filter, Finset.mem_univ,
    true_and]

lemma fixedIn_card_lt_of_none {n b : ℕ} (ρ : Part n b) {i : Fin n} {j : Fin b}
    (h : ρ ⟨i, j⟩ = none) :
    (fixedIn ρ i).card < b := by
  have hj : j ∉ fixedIn ρ i := by simp [fixedIn, h]
  have hlt : (fixedIn ρ i).card < (Finset.univ : Finset (Fin b)).card :=
    Finset.card_lt_card (Finset.ssubset_univ_iff.2 (fun he => hj (he ▸ Finset.mem_univ j)))
  simpa using hlt

lemma fixedIn_stepRho_eq {n b : ℕ} (v : List Bool → RawT n b) (q : List Bool) (bit : Bool)
    (ρ : Part n b) (i : Fin n) (h : (v q).1 ≠ i ∨ (ρ (v q)).isSome) :
    fixedIn (stepRho v q bit ρ) i = fixedIn ρ i := by
  ext j
  simp only [fixedIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases h with hne | hsome
  · have hu : (⟨i, j⟩ : RawT n b) ≠ v q := fun e => hne (by rw [← e])
    rw [stepRho_ne v q bit ρ hu]
  · unfold stepRho
    cases hq : ρ (v q) with
    | none => simp [hq] at hsome
    | some _ => rfl

lemma fixedIn_stepRho_insert {n b : ℕ} (v : List Bool → RawT n b) (q : List Bool) (bit : Bool)
    (ρ : Part n b) (i : Fin n) (hi : (v q).1 = i) (hnone : ρ (v q) = none) :
    fixedIn (stepRho v q bit ρ) i = insert (v q).2 (fixedIn ρ i) := by
  ext j
  simp only [fixedIn, Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and, stepRho, hnone]
  by_cases hj : j = (v q).2
  · subst hj
    have hu : (⟨i, (v q).2⟩ : RawT n b) = v q := by
      cases hv : v q with
      | mk a c => simp [hv] at hi ⊢; exact hi.symm
    rw [hu, Function.update_self]; simp
  · have hu : (⟨i, j⟩ : RawT n b) ≠ v q := fun e => hj (by
      cases hv : v q with
      | mk a c =>
        simp [hv] at hi e
        rcases e with ⟨rfl, h2⟩
        exact h2)
    rw [Function.update_of_ne hu]; simp [hj]

lemma onesIn_stepRho_eq {n b : ℕ} (v : List Bool → RawT n b) (q : List Bool) (bit : Bool)
    (ρ : Part n b) (i : Fin n) (h : (v q).1 ≠ i ∨ (ρ (v q)).isSome) :
    onesIn (stepRho v q bit ρ) i = onesIn ρ i := by
  ext j
  simp only [onesIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases h with hne | hsome
  · have hu : (⟨i, j⟩ : RawT n b) ≠ v q := fun e => hne (by rw [← e])
    rw [stepRho_ne v q bit ρ hu]
  · unfold stepRho
    cases hq : ρ (v q) with
    | none => simp [hq] at hsome
    | some _ => rfl

lemma onesIn_stepRho_none {n b : ℕ} (v : List Bool → RawT n b) (q : List Bool) (bit : Bool)
    (ρ : Part n b) (i : Fin n) (hi : (v q).1 = i) (hnone : ρ (v q) = none) :
    onesIn (stepRho v q bit ρ) i =
      if bit = true then insert (v q).2 (onesIn ρ i) else onesIn ρ i := by
  ext j
  simp only [onesIn, Finset.mem_filter, Finset.mem_univ, true_and, stepRho, hnone]
  by_cases hj : j = (v q).2
  · subst hj
    have hu : (⟨i, (v q).2⟩ : RawT n b) = v q := by
      cases hv : v q with
      | mk a c => simp [hv] at hi ⊢; exact hi.symm
    rw [hu, Function.update_self]
    cases bit <;> simp [hnone, hu]
  · have hu : (⟨i, j⟩ : RawT n b) ≠ v q := fun e => hj (by
      cases hv : v q with
      | mk a c =>
        simp [hv] at hi e
        rcases e with ⟨rfl, h2⟩
        exact h2)
    rw [Function.update_of_ne hu]
    cases bit <;> simp [hj]

lemma parity_xor_bool (k : ℕ) (x : Bool) :
    decide (Odd (k + if (decide (Odd k) != x) = true then 1 else 0)) = x := by
  cases x <;> by_cases hk : Odd k
  · simp [hk, Nat.odd_add_one]
  · simp [hk]
  · simp [hk]
  · simp [hk, Nat.odd_add_one]

def ValidWalk {n b : ℕ} (J : Finset (List Bool)) (v : List Bool → RawT n b)
    (r : RVec n b) (x : Fin n → Bool) (p : List Bool) : Prop :=
  ∀ (t : ℕ) (ht : t < p.length),
    p.take t ∈ J ∧ p[t] = stepBit v r x (p.take t) (pathRho v (p.take t))

lemma validWalk_nil {n b : ℕ} (J : Finset (List Bool)) (v : List Bool → RawT n b)
    (r : RVec n b) (x : Fin n → Bool) :
    ValidWalk J v r x [] := by
  intro t ht; simp at ht

lemma validWalk_append_singleton {n b : ℕ} (J : Finset (List Bool)) (v : List Bool → RawT n b)
    (r : RVec n b) (x : Fin n → Bool) (p : List Bool) (hp : p ∈ J)
    (hvw : ValidWalk J v r x p) :
    ValidWalk J v r x (p ++ [stepBit v r x p (pathRho v p)]) := by
  intro t ht
  rw [List.length_append, List.length_singleton] at ht
  by_cases hlt : t < p.length
  · rw [List.take_append_of_le_length (le_of_lt hlt), List.getElem_append_left hlt]
    exact hvw t hlt
  · have hteq : t = p.length := by omega
    subst hteq
    simp [hp]

def walkFrom {n b : ℕ} (J : Finset (List Bool)) (v : List Bool → RawT n b)
    (r : RVec n b) (x : Fin n → Bool) : ℕ → List Bool → Part n b → List Bool
  | 0, p, _ => p
  | fuel + 1, p, ρ =>
    if p ∈ J then
      let bit := stepBit v r x p ρ
      walkFrom J v r x fuel (p ++ [bit]) (stepRho v p bit ρ)
    else
      p

lemma walkFrom_spec {n b : ℕ} (N J : Finset (List Bool)) (v : List Bool → RawT n b)
    (hch : ∀ q ∈ J, q ++ [false] ∈ N ∧ q ++ [true] ∈ N)
    (r : RVec n b) (x : Fin n → Bool) :
    ∀ (fuel : ℕ) (p : List Bool),
      p ∈ N → N.sup List.length - p.length < fuel → ValidWalk J v r x p →
      walkFrom J v r x fuel p (pathRho v p) ∈ N \ J ∧
      ValidWalk J v r x (walkFrom J v r x fuel p (pathRho v p)) := by
  intro fuel
  induction fuel with
  | zero => intro p _ hlt _; omega
  | succ fuel ih =>
    intro p hpN hlt hvw
    unfold walkFrom
    split_ifs with hpJ
    · set bit := stepBit v r x p (pathRho v p)
      have hp'N : p ++ [bit] ∈ N := by
        cases hbit : bit
        · exact (hch p hpJ).1
        · exact (hch p hpJ).2
      have hlen : (p ++ [bit]).length ≤ N.sup List.length :=
        Finset.le_sup (f := List.length) hp'N
      have hlt' : N.sup List.length - (p ++ [bit]).length < fuel := by
        rw [List.length_append, List.length_singleton] at hlen ⊢
        omega
      dsimp only
      rw [← pathRho_append_singleton v p bit]
      exact ih (p ++ [bit]) hp'N hlt' (validWalk_append_singleton J v r x p hpJ hvw)
    · exact ⟨Finset.mem_sdiff.2 ⟨hpN, hpJ⟩, hvw⟩

def leaf {n b : ℕ} (N J : Finset (List Bool)) (v : List Bool → RawT n b)
    (r : RVec n b) (x : Fin n → Bool) : List Bool :=
  walkFrom J v r x (N.sup List.length + 1) [] (fun _ => none)

lemma leaf_spec {n b : ℕ} (N J : Finset (List Bool)) (v : List Bool → RawT n b)
    (h0 : [] ∈ N) (hch : ∀ q ∈ J, q ++ [false] ∈ N ∧ q ++ [true] ∈ N)
    (r : RVec n b) (x : Fin n → Bool) :
    leaf N J v r x ∈ N \ J ∧ ValidWalk J v r x (leaf N J v r x) := by
  simpa [leaf, pathRho, pathRhoAux] using
    walkFrom_spec N J v hch r x (N.sup List.length + 1) [] h0 (by simp) (validWalk_nil J v r x)

lemma validWalk_unique {n b : ℕ} (N J : Finset (List Bool)) (v : List Bool → RawT n b)
    (r : RVec n b) (x : Fin n → Bool) {p₁ p₂ : List Bool}
    (h1 : p₁ ∈ N \ J) (h2 : p₂ ∈ N \ J)
    (hv1 : ValidWalk J v r x p₁) (hv2 : ValidWalk J v r x p₂) :
    p₁ = p₂ := by
  have htake : ∀ k, k ≤ p₁.length → k ≤ p₂.length → p₁.take k = p₂.take k := by
    intro k
    induction k with
    | zero => intro _ _; simp
    | succ k ih =>
      intro hk1 hk2
      have h1k : k < p₁.length := by omega
      have h2k : k < p₂.length := by omega
      have heq := ih (le_of_lt h1k) (le_of_lt h2k)
      rw [List.take_succ_eq_append_getElem h1k, List.take_succ_eq_append_getElem h2k, heq]
      congr 1
      have e1 := (hv1 k h1k).2
      have e2 := (hv2 k h2k).2
      rw [heq] at e1
      rw [e1, ← e2]
  rcases lt_trichotomy p₁.length p₂.length with hlt | heq | hgt
  · have ht := htake p₁.length le_rfl (le_of_lt hlt)
    rw [List.take_length] at ht
    have hmem : p₁ ∈ J := ht ▸ (hv2 p₁.length hlt).1
    exact ((Finset.mem_sdiff.1 h1).2 hmem).elim
  · have ht := htake p₁.length le_rfl (le_of_eq heq)
    rw [List.take_length, heq, List.take_length] at ht
    exact ht
  · have ht := htake p₂.length (le_of_lt hgt) le_rfl
    rw [List.take_length] at ht
    have hmem : p₂ ∈ J := ht.symm ▸ (hv1 p₂.length hgt).1
    exact ((Finset.mem_sdiff.1 h2).2 hmem).elim

lemma validWalk_transfer_x {n b : ℕ} (hb : 0 < b) (J : Finset (List Bool))
    (v : List Bool → RawT n b) (r : RVec n b) (x₁ x₂ : Fin n → Bool) (p : List Bool)
    (hvw : ValidWalk J v r x₁ p)
    (hx : ∀ i ∈ fullBlocks (pathRho v p), x₂ i = x₁ i) :
    ValidWalk J v r x₂ p := by
  intro t ht
  obtain ⟨htJ, hbit⟩ := hvw t ht
  refine ⟨htJ, ?_⟩
  rw [hbit]
  unfold stepBit
  cases hnone : pathRho v (p.take t) (v (p.take t)) with
  | some _ => rfl
  | none =>
    simp only
    split_ifs with hlt
    · rfl
    · have hcard_lt : (fixedIn (pathRho v (p.take t)) (v (p.take t)).1).card < b :=
        fixedIn_card_lt_of_none (pathRho v (p.take t)) (by simpa using hnone)
      have hcard_eq : (fixedIn (pathRho v (p.take t)) (v (p.take t)).1).card = b - 1 := by omega
      have hfull_next : (v (p.take t)).1 ∈ fullBlocks (pathRho v (p.take (t + 1))) := by
        rw [← fixedIn_card_eq_iff, List.take_succ_eq_append_getElem ht, pathRho_append_singleton]
        rw [fixedIn_stepRho_insert v _ _ _ _ rfl hnone]
        have hnot : (v (p.take t)).2 ∉ fixedIn (pathRho v (p.take t)) (v (p.take t)).1 := by
          simp [fixedIn, hnone]
        rw [Finset.card_insert_of_notMem hnot, hcard_eq]
        omega
      have hfull_p : (v (p.take t)).1 ∈ fullBlocks (pathRho v p) := by
        have hmono := fullBlocks_take_mono v p (show t + 1 ≤ p.length by omega) hfull_next
        simpa using hmono
      rw [hx _ hfull_p]

lemma exists_step_of_nat_jump (f : ℕ → ℕ) (L m : ℕ)
    (h0 : f 0 = 0) (hL : m < f L)
    (hstep : ∀ t < L, f (t + 1) = f t ∨ f (t + 1) = f t + 1) :
    ∃ t < L, f t = m ∧ f (t + 1) = m + 1 := by
  induction L with
  | zero => omega
  | succ L ih =>
    by_cases hprev : m < f L
    · obtain ⟨t, ht, h1, h2⟩ := ih hprev (fun t ht => hstep t (by omega))
      exact ⟨t, by omega, h1, h2⟩
    · have hs := hstep L (by omega)
      rcases hs with heq | hinc
      · omega
      · exact ⟨L, by omega, by omega, by omega⟩

lemma validWalk_unique_r {n b : ℕ} (J : Finset (List Bool)) (v : List Bool → RawT n b)
    (r₁ r₂ : RVec n b) (x₁ x₂ : Fin n → Bool) (p : List Bool)
    (hv1 : ValidWalk J v r₁ x₁ p) (hv2 : ValidWalk J v r₂ x₂ p)
    (i : Fin n) (hi : i ∈ fullBlocks (pathRho v p)) :
    r₁ i = r₂ i := by
  funext m
  let f : ℕ → ℕ := fun t => (fixedIn (pathRho v (p.take t)) i).card
  have hf0 : f 0 = 0 := by simp [f, fixedIn, pathRho, pathRhoAux]
  have hfL : m.val < f p.length := by
    have : f p.length = b := by
      simp only [f, List.take_length]
      exact (fixedIn_card_eq_iff _ _).2 hi
    omega
  have hfstep : ∀ t < p.length, f (t + 1) = f t ∨ f (t + 1) = f t + 1 := by
    intro t ht
    simp only [f, List.take_succ_eq_append_getElem ht, pathRho_append_singleton]
    by_cases hcond : (v (p.take t)).1 = i ∧ pathRho v (p.take t) (v (p.take t)) = none
    · right
      rw [fixedIn_stepRho_insert v _ _ _ _ hcond.1 hcond.2]
      have hnot : (v (p.take t)).2 ∉ fixedIn (pathRho v (p.take t)) i := by
        simp [fixedIn, ← hcond.1, hcond.2]
      exact Finset.card_insert_of_notMem hnot
    · left
      rw [fixedIn_stepRho_eq v _ _ _ _ (by
        by_cases h1 : (v (p.take t)).1 = i
        · right
          cases h2 : pathRho v (p.take t) (v (p.take t)) with
          | none => exact (hcond ⟨h1, h2⟩).elim
          | some _ => rfl
        · exact Or.inl h1)]
  obtain ⟨t, ht, hft, hft1⟩ := exists_step_of_nat_jump f p.length m.val hf0 hfL hfstep
  have hcond : (v (p.take t)).1 = i ∧ pathRho v (p.take t) (v (p.take t)) = none := by
    by_contra hnc
    have heq : f (t + 1) = f t := by
      simp only [f, List.take_succ_eq_append_getElem ht, pathRho_append_singleton]
      rw [fixedIn_stepRho_eq v _ _ _ _ (by
        by_cases h1 : (v (p.take t)).1 = i
        · right
          cases h2 : pathRho v (p.take t) (v (p.take t)) with
          | none => exact (hnc ⟨h1, h2⟩).elim
          | some _ => rfl
        · exact Or.inl h1)]
    omega
  have e1 := (hv1 t ht).2
  have e2 := (hv2 t ht).2
  unfold stepBit at e1 e2
  rw [hcond.2] at e1 e2
  simp only [hcond.1] at e1 e2
  have hm : (fixedIn (pathRho v (p.take t)) i).card < b - 1 := by
    change f t < b - 1; omega
  simp only [hm, ↓reduceDIte] at e1 e2
  have hfin : (⟨(fixedIn (pathRho v (p.take t)) i).card, hm⟩ : Fin (b - 1)) = m := by
    ext; exact hft
  rw [hfin] at e1 e2
  rw [← e1, e2]

lemma card_r_reaching_le {n b : ℕ} (N J : Finset (List Bool)) (v : List Bool → RawT n b)
    (h0 : [] ∈ N) (hch : ∀ q ∈ J, q ++ [false] ∈ N ∧ q ++ [true] ∈ N)
    (p : List Bool) :
    ((Finset.univ : Finset (RVec n b)).filter (fun r => ∃ x, leaf N J v r x = p)).card ≤
      (2 ^ (b - 1)) ^ (n - (fullBlocks (pathRho v p)).card) := by
  classical
  set S := (Finset.univ : Finset (RVec n b)).filter (fun r => ∃ x, leaf N J v r x = p)
  by_cases hS : S.Nonempty
  · obtain ⟨r₀, hr₀⟩ := hS
    have hr₀' : ∃ x, leaf N J v r₀ x = p := (Finset.mem_filter.1 hr₀).2
    obtain ⟨x₀, hx₀⟩ := hr₀'
    have hvw₀ : ValidWalk J v r₀ x₀ p := hx₀ ▸ (leaf_spec N J v h0 hch r₀ x₀).2
    let K := fullBlocks (pathRho v p)
    let proj : RVec n b → ({i : Fin n // i ∉ K} → Fin (b - 1) → Bool) :=
      fun r ⟨i, _⟩ => r i
    have hinj : Set.InjOn proj S := by
      intro r₁ hr₁ r₂ hr₂ heq
      obtain ⟨x₁, hx₁⟩ := (Finset.mem_filter.1 hr₁).2
      obtain ⟨x₂, hx₂⟩ := (Finset.mem_filter.1 hr₂).2
      have hvw1 : ValidWalk J v r₁ x₁ p := hx₁ ▸ (leaf_spec N J v h0 hch r₁ x₁).2
      have hvw2 : ValidWalk J v r₂ x₂ p := hx₂ ▸ (leaf_spec N J v h0 hch r₂ x₂).2
      funext i
      by_cases hi : i ∈ K
      · exact validWalk_unique_r J v r₁ r₂ x₁ x₂ p hvw1 hvw2 i hi
      · exact congrFun heq ⟨i, hi⟩
    have hle := Finset.card_le_card_of_injOn proj (fun _ _ => Finset.mem_univ _) hinj
    refine le_trans hle ?_
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    have hcard : Fintype.card {i : Fin n // i ∉ K} = n - K.card := by
      have h1 : Fintype.card {i : Fin n // i ∉ K} = ((Finset.univ : Finset (Fin n)) \ K).card := by
        rw [Fintype.card_subtype]
        congr 1
        ext i; simp
      rw [h1, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    rw [hcard]
  · rw [Finset.not_nonempty_iff_eq_empty.1 hS, Finset.card_empty]
    exact Nat.zero_le _

lemma validWalk_parity {n b : ℕ} (hb : 0 < b) (J : Finset (List Bool))
    (v : List Bool → RawT n b) (r : RVec n b) (x : Fin n → Bool) (p : List Bool)
    (hvw : ValidWalk J v r x p) :
    ∀ t ≤ p.length, ∀ i ∈ fullBlocks (pathRho v (p.take t)),
      decide (Odd (onesIn (pathRho v (p.take t)) i).card) = x i := by
  intro t
  induction t with
  | zero =>
    intro _ i hi
    simp only [fullBlocks, Finset.mem_filter, Finset.mem_univ, true_and, List.take_zero,
      pathRho, pathRhoAux] at hi
    have := hi ⟨0, hb⟩
    simp at this
  | succ t ih =>
    intro ht i hi
    have hlt : t < p.length := by omega
    by_cases hprev : i ∈ fullBlocks (pathRho v (p.take t))
    · have hsome : (v (p.take t)).1 ≠ i ∨ (pathRho v (p.take t) (v (p.take t))).isSome := by
        by_cases h1 : (v (p.take t)).1 = i
        · right
          simp only [fullBlocks, Finset.mem_filter, Finset.mem_univ, true_and] at hprev
          have := hprev (v (p.take t)).2
          rwa [← h1] at this
        · exact Or.inl h1
      rw [List.take_succ_eq_append_getElem hlt, pathRho_append_singleton,
        onesIn_stepRho_eq v _ _ _ _ hsome]
      exact ih (le_of_lt hlt) i hprev
    · have hcond : (v (p.take t)).1 = i ∧ pathRho v (p.take t) (v (p.take t)) = none := by
        by_contra hnc
        have heq : fixedIn (pathRho v (p.take (t + 1))) i = fixedIn (pathRho v (p.take t)) i := by
          rw [List.take_succ_eq_append_getElem hlt, pathRho_append_singleton]
          exact fixedIn_stepRho_eq v _ _ _ _ (by
            by_cases h1 : (v (p.take t)).1 = i
            · right
              cases h2 : pathRho v (p.take t) (v (p.take t)) with
              | none => exact (hnc ⟨h1, h2⟩).elim
              | some _ => rfl
            · exact Or.inl h1)
        have hfull : i ∈ fullBlocks (pathRho v (p.take t)) := by
          rw [← fixedIn_card_eq_iff, ← heq, fixedIn_card_eq_iff]
          exact hi
        exact hprev hfull
      have hcard_eq : (fixedIn (pathRho v (p.take t)) i).card = b - 1 := by
        have h1 : (fixedIn (pathRho v (p.take (t + 1))) i).card = b :=
          (fixedIn_card_eq_iff _ _).2 hi
        rw [List.take_succ_eq_append_getElem hlt, pathRho_append_singleton,
          fixedIn_stepRho_insert v _ _ _ _ hcond.1 hcond.2] at h1
        have hnot : (v (p.take t)).2 ∉ fixedIn (pathRho v (p.take t)) i := by
          simp [fixedIn, ← hcond.1, hcond.2]
        rw [Finset.card_insert_of_notMem hnot] at h1
        omega
      have hbit := (hvw t hlt).2
      unfold stepBit at hbit
      rw [hcond.2] at hbit
      simp only [hcond.1, hcard_eq] at hbit
      have hnot_lt : ¬ b - 1 < b - 1 := Nat.lt_irrefl _
      simp only [hnot_lt, ↓reduceDIte] at hbit
      rw [List.take_succ_eq_append_getElem hlt, pathRho_append_singleton,
        onesIn_stepRho_none v _ _ _ _ hcond.1 hcond.2, hbit]
      have hnot_ones : (v (p.take t)).2 ∉ onesIn (pathRho v (p.take t)) i := by
        simp [onesIn, ← hcond.1, hcond.2]
      have hcard_ones :
          (if (decide (Odd (onesIn (pathRho v (p.take t)) i).card) != x i) = true then
              insert (v (p.take t)).2 (onesIn (pathRho v (p.take t)) i)
            else onesIn (pathRho v (p.take t)) i).card =
          (onesIn (pathRho v (p.take t)) i).card +
            if (decide (Odd (onesIn (pathRho v (p.take t)) i).card) != x i) = true then 1 else 0 := by
        split_ifs
        · rw [Finset.card_insert_of_notMem hnot_ones]
        · simp
      rw [hcard_ones]
      exact parity_xor_bool _ _

lemma validWalk_not_sat {n b : ℕ} (J : Finset (List Bool))
    (line : List Bool → Clause (RawT n b)) (v : List Bool → RawT n b)
    (hline0 : line [] = ∅)
    (hres : ∀ q ∈ J,
      (v q, true) ∈ line (q ++ [false]) ∧ (v q, false) ∈ line (q ++ [true]) ∧
      line q = (line (q ++ [false])).erase (v q, true) ∪ (line (q ++ [true])).erase (v q, false))
    (r : RVec n b) (x : Fin n → Bool) (p : List Bool) (hvw : ValidWalk J v r x p) :
    ∀ t ≤ p.length, ∀ y : RawT n b → Bool,
      agrees y (pathRho v (p.take t)) → ¬ ClauseSat y (line (p.take t)) := by
  intro t
  induction t with
  | zero =>
    intro _ y _ hsat
    obtain ⟨l, hl, _⟩ := hsat
    simp [hline0] at hl
  | succ t ih =>
    intro ht y hag hsat
    have hlt : t < p.length := by omega
    have hag_prev : agrees y (pathRho v (p.take t)) := fun u c hc =>
      hag u c (pathRho_take_mono v p (Nat.le_succ t) hc)
    have hnsat_prev := ih (le_of_lt hlt) y hag_prev
    obtain ⟨htJ, hbit⟩ := hvw t hlt
    have hyv : y (v (p.take t)) = p[t] := by
      cases hq : pathRho v (p.take t) (v (p.take t)) with
      | some c =>
        have hc : p[t] = c := by
          rw [hbit]; unfold stepBit; rw [hq]
        rw [hc]
        exact hag_prev (v (p.take t)) c hq
      | none =>
        have hstep : pathRho v (p.take (t + 1)) (v (p.take t)) = some p[t] := by
          rw [List.take_succ_eq_append_getElem hlt, pathRho_append_singleton]
          simp only [stepRho, hq, Function.update_self]
        exact hag (v (p.take t)) p[t] hstep
    obtain ⟨_, _, hleq⟩ := hres (p.take t) htJ
    rw [List.take_succ_eq_append_getElem hlt] at hsat
    obtain ⟨l, hl, hyl⟩ := hsat
    cases hpt : p[t]
    · rw [hpt] at hl hyv
      by_cases hle : l = (v (p.take t), true)
      · subst hle; simp [hyv] at hyl
      · apply hnsat_prev
        refine ⟨l, ?_, hyl⟩
        rw [hleq]
        exact Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hle, hl⟩)
    · rw [hpt] at hl hyv
      by_cases hle : l = (v (p.take t), false)
      · subst hle; simp [hyv] at hyl
      · apply hnsat_prev
        refine ⟨l, ?_, hyl⟩
        rw [hleq]
        exact Finset.mem_union_right _ (Finset.mem_erase.2 ⟨hle, hl⟩)

lemma exists_ext_parity {n b : ℕ} (hb : 0 < b) (J : Finset (List Bool))
    (v : List Bool → RawT n b) (r : RVec n b) (x : Fin n → Bool) (p : List Bool)
    (hvw : ValidWalk J v r x p) :
    ∃ y : RawT n b → Bool, agrees y (pathRho v p) ∧ ∀ i : Fin n, parityFn y i = x i := by
  classical
  let ρ := pathRho v p
  let pick (i : Fin n) (hi : i ∉ fullBlocks ρ) : Fin b :=
    Classical.choose (by
      simp only [fullBlocks, Finset.mem_filter, Finset.mem_univ, true_and, not_forall] at hi
      exact hi)
  have hpick_none : ∀ (i : Fin n) (hi : i ∉ fullBlocks ρ), ρ ⟨i, pick i hi⟩ = none := by
    intro i hi
    have hspec := Classical.choose_spec (show ∃ j : Fin b, ¬(ρ ⟨i, j⟩).isSome by
      simp only [fullBlocks, Finset.mem_filter, Finset.mem_univ, true_and, not_forall] at hi
      exact hi)
    change ¬(ρ ⟨i, pick i hi⟩).isSome at hspec
    cases h : ρ ⟨i, pick i hi⟩ with
    | none => rfl
    | some _ => rw [h] at hspec; simp at hspec
  let y : RawT n b → Bool := fun u =>
    if hi : u.1 ∈ fullBlocks ρ then
      (ρ u).getD false
    else if u.2 = pick u.1 hi then
      decide (Odd (onesIn ρ u.1).card) != x u.1
    else
      (ρ u).getD false
  refine ⟨y, ?_, ?_⟩
  · intro u c hc
    change ρ u = some c at hc
    dsimp only [y]
    split_ifs with hi hjeq
    · simp [hc]
    · have hnone := hpick_none u.1 hi
      have heq : (⟨u.1, pick u.1 hi⟩ : RawT n b) = u := by
        cases u; simp at hjeq; simp [hjeq]
      rw [heq, hc] at hnone
      cases hnone
    · simp [hc]
  · intro i
    unfold parityFn
    by_cases hi : i ∈ fullBlocks ρ
    · have hset : (Finset.univ.filter fun j : Fin b => y ⟨i, j⟩ = true) = onesIn ρ i := by
        ext j
        simp only [onesIn, Finset.mem_filter, Finset.mem_univ, true_and, y, hi, ↓reduceDIte]
        cases hc : ρ ⟨i, j⟩ with
        | none =>
          simp only [fullBlocks, Finset.mem_filter, Finset.mem_univ, true_and] at hi
          have := hi j; simp [hc] at this
        | some c => cases c <;> simp
      rw [hset]
      have hp := validWalk_parity hb J v r x p hvw p.length le_rfl i (by simpa [ρ] using hi)
      simpa [ρ] using hp
    · let j₀ := pick i hi
      let bit := decide (Odd (onesIn ρ i).card) != x i
      have hnot : j₀ ∉ onesIn ρ i := by
        simp [onesIn, j₀, hpick_none i hi]
      have hy_j0 : y ⟨i, j₀⟩ = bit := by
        simp only [y, hi, ↓reduceDIte, j₀, ↓reduceIte, bit]
      have hy_ne : ∀ j : Fin b, j ≠ j₀ → y ⟨i, j⟩ = (ρ ⟨i, j⟩).getD false := by
        intro j hj
        simp only [y, hi, ↓reduceDIte, show j ≠ pick i hi from hj, ↓reduceIte]
      have hset : (Finset.univ.filter fun j : Fin b => y ⟨i, j⟩ = true) =
          if bit = true then insert j₀ (onesIn ρ i) else onesIn ρ i := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        by_cases hj : j = j₀
        · subst hj
          rw [hy_j0]
          cases hbit : bit <;> simp [hnot]
        · rw [hy_ne j hj]
          have hmem : (ρ ⟨i, j⟩).getD false = true ↔ j ∈ onesIn ρ i := by
            simp only [onesIn, Finset.mem_filter, Finset.mem_univ, true_and]
            cases hc : ρ ⟨i, j⟩ with
            | none => simp
            | some c => cases c <;> simp
          rw [hmem]
          cases hbit : bit <;> simp [hj]
      rw [hset]
      have hcard : (if bit = true then insert j₀ (onesIn ρ i) else onesIn ρ i).card =
          (onesIn ρ i).card + if bit = true then 1 else 0 := by
        split_ifs
        · rw [Finset.card_insert_of_notMem hnot]
        · simp
      rw [hcard]
      exact parity_xor_bool _ _

lemma minimal_no_taut {n : ℕ} (F : Finset (Clause (Fin n)))
    (hunsat : ¬ Satisfiable (F : Set (Clause (Fin n))))
    (hmin : ∀ C ∈ F, Satisfiable (↑(F.erase C) : Set (Clause (Fin n))))
    {C : Clause (Fin n)} (hCF : C ∈ F) :
    (C.image Prod.fst).card = C.card := by
  apply Finset.card_image_of_injOn
  intro l₁ hl₁ l₂ hl₂ hfst
  rcases l₁ with ⟨i₁, b₁⟩
  rcases l₂ with ⟨i₂, b₂⟩
  simp only at hfst
  subst hfst
  by_cases hb : b₁ = b₂
  · subst hb; rfl
  · exfalso
    obtain ⟨x, hx⟩ := hmin C hCF
    apply hunsat
    refine ⟨x, fun D hD => ?_⟩
    by_cases hDC : D = C
    · subst hDC
      cases hb1 : b₁ <;> cases hb2 : b₂
      · exact (hb (hb1.trans hb2.symm)).elim
      · cases hx1 : x i₁
        · exact ⟨(i₁, false), hb1 ▸ hl₁, hx1⟩
        · exact ⟨(i₁, true), hb2 ▸ hl₂, hx1⟩
      · cases hx1 : x i₁
        · exact ⟨(i₁, false), hb2 ▸ hl₂, hx1⟩
        · exact ⟨(i₁, true), hb1 ▸ hl₁, hx1⟩
      · exact (hb (hb1.trans hb2.symm)).elim
    · exact hx D (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hDC, hD⟩))

lemma exists_le_avg {α : Type*} [Fintype α] (hne : Nonempty α) (g : α → ℕ) (B : ℕ)
    (hsum : ∑ r : α, g r ≤ B * Fintype.card α) :
    ∃ r : α, g r ≤ B := by
  by_contra h
  push Not at h
  have h1 : ∑ _r : α, (B + 1) ≤ ∑ r : α, g r :=
    Finset.sum_le_sum (fun r _ => h r)
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h1
  have hpos : 0 < Fintype.card α := Fintype.card_pos_iff.2 hne
  nlinarith

end PEqualNP.Outside.L_pcx_327_aux

theorem PEqualNP.Outside.L_pcx_327 : (∀ (n b : ℕ), 0 < b →
  let w := fun (_ : Fin n) => b
  let Raw := (i : Fin n) × Fin (w i)
  let parity := fun (y : Raw → Bool) (i : Fin n) =>
    decide (Odd ((Finset.univ : Finset (Fin (w i))).filter (fun j => y ⟨i,j⟩ = true)).card)
  let liftAx := fun (F : Set (PEqualNP.ProofComplexity.Clause (Fin n)))
      (A : PEqualNP.ProofComplexity.Clause Raw) =>
    ∃ C ∈ F, ∃ y : Raw → Bool, (∀ lit ∈ C, parity y lit.1 ≠ lit.2) ∧
      A = ((Finset.univ : Finset Raw).filter (fun b => b.1 ∈ C.image Prod.fst)).image
        (fun b => (b, !(y b)))
  let shape := fun (N J : Finset (List Bool)) =>
    [] ∈ N ∧ J ⊆ N ∧
    (∀ (p : List Bool) (b : Bool), p ++ [b] ∈ N → p ∈ J) ∧
    ∀ p ∈ J, p ++ [false] ∈ N ∧ p ++ [true] ∈ N
  ∀ F : Finset (PEqualNP.ProofComplexity.Clause (Fin n)),
    (¬ PEqualNP.ProofComplexity.Satisfiable (F : Set (PEqualNP.ProofComplexity.Clause (Fin n)))) →
    (∀ C ∈ F, PEqualNP.ProofComplexity.Satisfiable (↑(F.erase C) : Set (PEqualNP.ProofComplexity.Clause (Fin n)))) →
    ∀ (N J : Finset (List Bool)) (line : List Bool → PEqualNP.ProofComplexity.Clause Raw),
      shape N J → line [] = ∅ → (∀ p ∈ N \ J, liftAx (F : Set (PEqualNP.ProofComplexity.Clause (Fin n))) (line p)) →
      (∀ p ∈ J, PEqualNP.ProofComplexity.IsResolvent
        (line (p ++ [false])) (line (p ++ [true])) (line p)) →
      let a := 2^(b-1)
      let cost := fun (C : PEqualNP.ProofComplexity.Clause (Fin n)) => a^C.card
      ∃ U ⊆ F,
        (∀ C ∈ F, ∀ D ∈ F, C ≠ D →
          (∃ x : Fin n → Bool, ¬ PEqualNP.ProofComplexity.ClauseSat x C ∧
                                 ¬ PEqualNP.ProofComplexity.ClauseSat x D) → C ∈ U ∨ D ∈ U) ∧
        F.sum cost + (a-1) * U.sum cost ≤ (N \ J).card) := by
  classical
  open PEqualNP.ProofComplexity PEqualNP.Outside.L_pcx_327_aux in
  intro n b hb w Raw parity liftAx shape F hunsat hmin N J line hshape hline0 hleaf hres a cost
  by_cases hn0 : n = 0
  · subst hn0
    have hF_ne : F.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty] at h
      subst h
      apply hunsat
      exact ⟨Fin.elim0, fun C hC => by simp at hC⟩
    have hF_eq : F = {∅} := by
      ext C
      simp only [Finset.mem_singleton]
      constructor
      · intro hCF
        ext l
        exact Fin.elim0 l.1
      · intro hCe
        subst hCe
        obtain ⟨C₀, hC₀⟩ := hF_ne
        have : C₀ = ∅ := by ext l; exact Fin.elim0 l.1
        exact this ▸ hC₀
    have hleaf_ne : (N \ J).Nonempty := by
      have hstep : ∀ fuel (p : List Bool), p ∈ N → N.sup List.length - p.length < fuel →
          (N \ J).Nonempty := by
        intro fuel
        induction fuel with
        | zero => intro p _ hlt; omega
        | succ fuel ih =>
          intro p hpN hlt
          by_cases hpJ : p ∈ J
          · have hp' := (hshape.2.2.2 p hpJ).1
            have hle : (p ++ [false]).length ≤ N.sup List.length :=
              Finset.le_sup (f := List.length) hp'
            rw [List.length_append, List.length_singleton] at hle
            exact ih (p ++ [false]) hp' (by rw [List.length_append, List.length_singleton]; omega)
          · exact ⟨p, Finset.mem_sdiff.2 ⟨hpN, hpJ⟩⟩
      exact hstep (N.sup List.length + 1) [] hshape.1 (by simp)
    refine ⟨∅, Finset.empty_subset F, ?_, ?_⟩
    · intro C hCF D hDF hne _
      rw [hF_eq] at hCF hDF
      simp at hCF hDF
      exact (hne (hCF.trans hDF.symm)).elim
    · rw [hF_eq]
      simp only [Finset.sum_singleton, Finset.sum_empty, mul_zero, add_zero, cost, Finset.card_empty,
        pow_zero]
      exact Finset.card_pos.2 hleaf_ne
  · have hRaw_inh : Nonempty (RawT n b) := ⟨⟨⟨0, Nat.pos_of_ne_zero hn0⟩, ⟨0, hb⟩⟩⟩
    let v : List Bool → RawT n b := fun q =>
      if hq : q ∈ J then Classical.choose (hres q hq) else Classical.arbitrary (RawT n b)
    have hv_spec : ∀ q ∈ J,
        (v q, true) ∈ line (q ++ [false]) ∧ (v q, false) ∈ line (q ++ [true]) ∧
        line q = (line (q ++ [false])).erase (v q, true) ∪ (line (q ++ [true])).erase (v q, false) := by
      intro q hq
      dsimp only [v]
      simp only [hq, ↓reduceDIte]
      exact Classical.choose_spec (hres q hq)
    let Lr : RVec n b → Finset (List Bool) := fun r =>
      (Finset.univ : Finset (Fin n → Bool)).image (fun x => leaf N J v r x)
    have hLr_sub : ∀ r, Lr r ⊆ N \ J := by
      intro r p hp
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 hp
      exact (leaf_spec N J v hshape.1 hshape.2.2.2 r x).1
    have hsum_bound :
        ∑ r : RVec n b, ∑ p ∈ Lr r, a ^ (fullBlocks (pathRho v p)).card ≤
          (N \ J).card * Fintype.card (RVec n b) := by
      have hswap :
          ∑ r : RVec n b, ∑ p ∈ Lr r, a ^ (fullBlocks (pathRho v p)).card =
          ∑ p ∈ N \ J,
            ((Finset.univ : Finset (RVec n b)).filter (fun r => p ∈ Lr r)).card *
              a ^ (fullBlocks (pathRho v p)).card := by
        calc
          ∑ r : RVec n b, ∑ p ∈ Lr r, a ^ (fullBlocks (pathRho v p)).card
              = ∑ r : RVec n b, ∑ p ∈ N \ J,
                  if p ∈ Lr r then a ^ (fullBlocks (pathRho v p)).card else 0 := by
                apply Finset.sum_congr rfl
                intro r _
                rw [← Finset.sum_filter]
                congr 1
                ext p
                simp only [Finset.mem_filter]
                exact ⟨fun hp => ⟨hLr_sub r hp, hp⟩, fun h => h.2⟩
          _ = ∑ p ∈ N \ J, ∑ r : RVec n b,
                if p ∈ Lr r then a ^ (fullBlocks (pathRho v p)).card else 0 := Finset.sum_comm
          _ = ∑ p ∈ N \ J,
                ((Finset.univ : Finset (RVec n b)).filter (fun r => p ∈ Lr r)).card *
                  a ^ (fullBlocks (pathRho v p)).card := by
                apply Finset.sum_congr rfl
                intro p _
                rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
      rw [hswap]
      have hcardR : Fintype.card (RVec n b) = a ^ n := by
        simp [RVec, a]
      rw [hcardR]
      calc
        ∑ p ∈ N \ J,
            ((Finset.univ : Finset (RVec n b)).filter (fun r => p ∈ Lr r)).card *
              a ^ (fullBlocks (pathRho v p)).card
            ≤ ∑ p ∈ N \ J, a ^ n := by
              apply Finset.sum_le_sum
              intro p _
              have hfilt : (Finset.univ : Finset (RVec n b)).filter (fun r => p ∈ Lr r) =
                  (Finset.univ : Finset (RVec n b)).filter (fun r => ∃ x, leaf N J v r x = p) := by
                ext r
                simp [Lr]
              rw [hfilt]
              have hc := card_r_reaching_le N J v hshape.1 hshape.2.2.2 p
              have hkle : (fullBlocks (pathRho v p)).card ≤ n := by
                have := Finset.card_le_univ (fullBlocks (pathRho v p))
                simpa using this
              calc
                ((Finset.univ : Finset (RVec n b)).filter (fun r => ∃ x, leaf N J v r x = p)).card *
                    a ^ (fullBlocks (pathRho v p)).card
                    ≤ a ^ (n - (fullBlocks (pathRho v p)).card) *
                        a ^ (fullBlocks (pathRho v p)).card :=
                      Nat.mul_le_mul_right _ (by simpa [a] using hc)
                _ = a ^ n := by
                      rw [← pow_add, Nat.sub_add_cancel hkle]
        _ = (N \ J).card * a ^ n := by
              rw [Finset.sum_const, smul_eq_mul]
    obtain ⟨r₀, hr₀⟩ := exists_le_avg ⟨fun _ _ => false⟩
      (fun r => ∑ p ∈ Lr r, a ^ (fullBlocks (pathRho v p)).card) (N \ J).card hsum_bound
    let L0 := Lr r₀
    have hL0_sub : L0 ⊆ N \ J := hLr_sub r₀
    let clOf : List Bool → Clause (Fin n) := fun p =>
      if hp : p ∈ N \ J then Classical.choose (hleaf p hp) else ∅
    have hclOf_spec : ∀ p ∈ N \ J,
        clOf p ∈ F ∧ ∃ y₀ : RawT n b → Bool,
          (∀ lit ∈ clOf p, parityFn y₀ lit.1 ≠ lit.2) ∧
          line p = ((Finset.univ : Finset (RawT n b)).filter
            (fun u => u.1 ∈ (clOf p).image Prod.fst)).image (fun u => (u, !(y₀ u))) := by
      intro p hp
      dsimp only [clOf]
      simp only [hp, ↓reduceDIte]
      exact Classical.choose_spec (hleaf p hp)
    have hleaf_props : ∀ x : Fin n → Bool,
        let p := leaf N J v r₀ x
        ¬ ClauseSat x (clOf p) ∧ (clOf p).image Prod.fst ⊆ fullBlocks (pathRho v p) := by
      intro x
      set p := leaf N J v r₀ x
      have hp_spec := leaf_spec N J v hshape.1 hshape.2.2.2 r₀ x
      obtain ⟨_, y₀, hy₀_fals, hlinep⟩ := hclOf_spec p hp_spec.1
      have hnot_sat_all : ∀ y : RawT n b → Bool, agrees y (pathRho v p) → ¬ ClauseSat y (line p) := by
        intro y hy
        simpa using validWalk_not_sat J line v hline0 hv_spec r₀ x p hp_spec.2 p.length le_rfl y (by simpa using hy)
      constructor
      · obtain ⟨y, hy_ag, hy_par⟩ := exists_ext_parity hb J v r₀ x p hp_spec.2
        have hy_nsat := hnot_sat_all y hy_ag
        have hy_eq : ∀ u : RawT n b, u.1 ∈ (clOf p).image Prod.fst → y u = y₀ u := by
          intro u hu
          by_contra hne
          apply hy_nsat
          refine ⟨(u, !(y₀ u)), ?_, ?_⟩
          · rw [hlinep]
            exact Finset.mem_image.2 ⟨u, Finset.mem_filter.2 ⟨Finset.mem_univ u, hu⟩, rfl⟩
          · cases hyu : y u <;> cases hy0u : y₀ u <;> simp_all
        intro ⟨lit, hlit, hxlit⟩
        have hpar_eq : parityFn y lit.1 = parityFn y₀ lit.1 := by
          have hfeq : ((Finset.univ : Finset (Fin b)).filter (fun j => y ⟨lit.1, j⟩ = true)) =
              ((Finset.univ : Finset (Fin b)).filter (fun j => y₀ ⟨lit.1, j⟩ = true)) := by
            ext j
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rw [hy_eq ⟨lit.1, j⟩ (Finset.mem_image.2 ⟨lit, hlit, rfl⟩)]
          simp only [parityFn, hfeq]
        have h1 : x lit.1 = parityFn y₀ lit.1 := by rw [← hy_par lit.1, hpar_eq]
        exact hy₀_fals lit hlit (h1.symm.trans hxlit)
      · intro i hi
        simp only [fullBlocks, Finset.mem_filter, Finset.mem_univ, true_and]
        intro j
        by_contra hnot
        have hnone : pathRho v p ⟨i, j⟩ = none := by
          cases h : pathRho v p ⟨i, j⟩ with
          | none => rfl
          | some _ => simp [h] at hnot
        let y' : RawT n b → Bool := fun u =>
          if u = ⟨i, j⟩ then !(y₀ ⟨i, j⟩) else (pathRho v p u).getD false
        have hy'_ag : agrees y' (pathRho v p) := by
          intro u c hc
          dsimp only [y']
          split_ifs with hu
          · subst hu; rw [hc] at hnone; cases hnone
          · simp [hc]
        apply hnot_sat_all y' hy'_ag
        refine ⟨(⟨i, j⟩, !(y₀ ⟨i, j⟩)), ?_, ?_⟩
        · rw [hlinep]
          exact Finset.mem_image.2 ⟨⟨i, j⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩, rfl⟩
        · simp [y']
    let U : Finset (Clause (Fin n)) :=
      F.filter (fun C => ¬ ∃ p ∈ L0, clOf p = C ∧ (fullBlocks (pathRho v p)).card = C.card)
    refine ⟨U, Finset.filter_subset _ F, ?_, ?_⟩
    · intro C hCF D hDF hCD ⟨x, hxC, hxD⟩
      by_contra hneither
      push Not at hneither
      have hC_good : ∃ p ∈ L0, clOf p = C ∧ (fullBlocks (pathRho v p)).card = C.card := by
        by_contra hng
        exact hneither.1 (Finset.mem_filter.2 ⟨hCF, hng⟩)
      have hD_good : ∃ p ∈ L0, clOf p = D ∧ (fullBlocks (pathRho v p)).card = D.card := by
        by_contra hng
        exact hneither.2 (Finset.mem_filter.2 ⟨hDF, hng⟩)
      obtain ⟨p₁, hp₁L, hp₁C, hp₁card⟩ := hC_good
      obtain ⟨p₂, hp₂L, hp₂D, hp₂card⟩ := hD_good
      obtain ⟨x₁, _, rfl⟩ := Finset.mem_image.1 hp₁L
      obtain ⟨x₂, _, rfl⟩ := Finset.mem_image.1 hp₂L
      have hp1_props := hleaf_props x₁
      have hp2_props := hleaf_props x₂
      dsimp only at hp1_props hp2_props
      rw [hp₁C] at hp1_props
      rw [hp₂D] at hp2_props
      have hK1 : fullBlocks (pathRho v (leaf N J v r₀ x₁)) = C.image Prod.fst := by
        apply (Finset.eq_of_subset_of_card_le hp1_props.2 _).symm
        rw [hp₁card, minimal_no_taut F hunsat hmin hCF]
      have hK2 : fullBlocks (pathRho v (leaf N J v r₀ x₂)) = D.image Prod.fst := by
        apply (Finset.eq_of_subset_of_card_le hp2_props.2 _).symm
        rw [hp₂card, minimal_no_taut F hunsat hmin hDF]
      have hx_eq1 : ∀ i ∈ fullBlocks (pathRho v (leaf N J v r₀ x₁)), x i = x₁ i := by
        intro i hi
        rw [hK1] at hi
        obtain ⟨⟨i', s⟩, hlC, hif⟩ := Finset.mem_image.1 hi
        simp only at hif
        subst i'
        have h1 : x i ≠ s := fun e => hxC ⟨(i, s), hlC, e⟩
        have h2 : x₁ i ≠ s := fun e => hp1_props.1 ⟨(i, s), hlC, e⟩
        cases hxi : x i <;> cases hx1i : x₁ i <;> cases s <;> simp_all
      have hx_eq2 : ∀ i ∈ fullBlocks (pathRho v (leaf N J v r₀ x₂)), x i = x₂ i := by
        intro i hi
        rw [hK2] at hi
        obtain ⟨⟨i', s⟩, hlD, hif⟩ := Finset.mem_image.1 hi
        simp only at hif
        subst i'
        have h1 : x i ≠ s := fun e => hxD ⟨(i, s), hlD, e⟩
        have h2 : x₂ i ≠ s := fun e => hp2_props.1 ⟨(i, s), hlD, e⟩
        cases hxi : x i <;> cases hx2i : x₂ i <;> cases s <;> simp_all
      have hvx1 : ValidWalk J v r₀ x (leaf N J v r₀ x₁) :=
        validWalk_transfer_x hb J v r₀ x₁ x _ (leaf_spec N J v hshape.1 hshape.2.2.2 r₀ x₁).2 hx_eq1
      have hvx2 : ValidWalk J v r₀ x (leaf N J v r₀ x₂) :=
        validWalk_transfer_x hb J v r₀ x₂ x _ (leaf_spec N J v hshape.1 hshape.2.2.2 r₀ x₂).2 hx_eq2
      have hp_eq : leaf N J v r₀ x₁ = leaf N J v r₀ x₂ :=
        validWalk_unique N J v r₀ x
          (leaf_spec N J v hshape.1 hshape.2.2.2 r₀ x₁).1
          (leaf_spec N J v hshape.1 hshape.2.2.2 r₀ x₂).1 hvx1 hvx2
      exact hCD (hp₁C.symm.trans (congrArg clOf hp_eq |>.trans hp₂D))
    · have ha_pos : 1 ≤ a := Nat.one_le_pow (b - 1) 2 (by norm_num)
      have hterm : ∀ C ∈ F,
          cost C + (if C ∈ U then (a - 1) * cost C else 0) ≤
            ∑ p ∈ L0.filter (fun p => clOf p = C), a ^ (fullBlocks (pathRho v p)).card := by
        intro C hCF
        obtain ⟨xC, hxC⟩ := hmin C hCF
        set pC := leaf N J v r₀ xC
        have hpC_L0 : pC ∈ L0 := Finset.mem_image.2 ⟨xC, Finset.mem_univ _, rfl⟩
        have hpC_clF : clOf pC ∈ F := (hclOf_spec pC (hL0_sub hpC_L0)).1
        have hpC_nsat : ¬ ClauseSat xC (clOf pC) := (hleaf_props xC).1
        have hpC_eq : clOf pC = C := by
          by_contra hne
          exact hpC_nsat (hxC (clOf pC) (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hne, hpC_clF⟩)))
        have hpC_filt : pC ∈ L0.filter (fun p => clOf p = C) :=
          Finset.mem_filter.2 ⟨hpC_L0, hpC_eq⟩
        have hcard_ge : C.card ≤ (fullBlocks (pathRho v pC)).card := by
          have hsub := (hleaf_props xC).2
          rw [hpC_eq] at hsub
          rw [← minimal_no_taut F hunsat hmin hCF]
          exact Finset.card_le_card hsub
        have hsingle : a ^ (fullBlocks (pathRho v pC)).card ≤
            ∑ p ∈ L0.filter (fun p => clOf p = C), a ^ (fullBlocks (pathRho v p)).card :=
          Finset.single_le_sum (f := fun p => a ^ (fullBlocks (pathRho v p)).card)
            (fun _ _ => Nat.zero_le _) hpC_filt
        split_ifs with hCU
        · have hne_card : (fullBlocks (pathRho v pC)).card ≠ C.card := by
            intro heq
            have hnotU := (Finset.mem_filter.1 hCU).2
            exact hnotU ⟨pC, hpC_L0, hpC_eq, heq⟩
          have hgt : C.card + 1 ≤ (fullBlocks (pathRho v pC)).card := by omega
          have hpow : a ^ (C.card + 1) ≤ a ^ (fullBlocks (pathRho v pC)).card :=
            Nat.pow_le_pow_right ha_pos hgt
          have halg : cost C + (a - 1) * cost C = a ^ (C.card + 1) := by
            simp only [cost, pow_succ']
            have : 1 + (a - 1) = a := by omega
            calc
              a ^ C.card + (a - 1) * a ^ C.card = (1 + (a - 1)) * a ^ C.card := by ring
              _ = a * a ^ C.card := by rw [this]
          exact halg ▸ le_trans hpow hsingle
        · rw [add_zero]
          exact le_trans (Nat.pow_le_pow_right ha_pos hcard_ge) hsingle
      have hUeq : F.filter (fun C => C ∈ U) = U := by
        ext C
        simp only [Finset.mem_filter, and_iff_right_iff_imp]
        exact fun hCU => (Finset.mem_filter.1 hCU).1
      have hLHS : F.sum cost + (a - 1) * U.sum cost =
          ∑ C ∈ F, (cost C + if C ∈ U then (a - 1) * cost C else 0) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_filter, hUeq, Finset.mul_sum]
      have hpart :
          ∑ C ∈ F, ∑ p ∈ L0.filter (fun p => clOf p = C), a ^ (fullBlocks (pathRho v p)).card =
            ∑ p ∈ L0, a ^ (fullBlocks (pathRho v p)).card := by
        rw [← Finset.sum_biUnion]
        · congr 1
          ext p
          simp only [Finset.mem_biUnion, Finset.mem_filter]
          constructor
          · rintro ⟨_, _, hp, _⟩; exact hp
          · intro hp; exact ⟨clOf p, (hclOf_spec p (hL0_sub hp)).1, hp, rfl⟩
        · intro C _ D _ hCD
          exact Finset.disjoint_left.2 (fun p hp1 hp2 =>
            hCD ((Finset.mem_filter.1 hp1).2.symm.trans (Finset.mem_filter.1 hp2).2))
      calc
        F.sum cost + (a - 1) * U.sum cost
            = ∑ C ∈ F, (cost C + if C ∈ U then (a - 1) * cost C else 0) := hLHS
        _ ≤ ∑ C ∈ F, ∑ p ∈ L0.filter (fun p => clOf p = C),
              a ^ (fullBlocks (pathRho v p)).card := Finset.sum_le_sum hterm
        _ = ∑ p ∈ L0, a ^ (fullBlocks (pathRho v p)).card := hpart
        _ ≤ (N \ J).card := hr₀
