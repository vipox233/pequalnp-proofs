import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_780_aux

open Module

abbrev V (n : ℕ) := Fin n → ZMod 2
abbrev P (n : ℕ) := ZMod 2 × (Fin n → ZMod 2)

lemma z2 (z : ZMod 2) : z = 0 ∨ z = 1 := by revert z; decide

lemma two_v {n : ℕ} (y : V n) : y + y = 0 := by
  funext i
  show y i + y i = 0
  generalize y i = a
  revert a; decide

lemma eq_of_add_v {n : ℕ} {x y : V n} (h : x + y = 0) : x = y := by
  funext i
  have := congrFun h i
  change x i + y i = 0 at this
  revert this
  generalize x i = a; generalize y i = b
  revert a b; decide

def Succ (n q : ℕ) (c : V n → ZMod 2) : Prop :=
  ∃ (ask : (j : Fin q) → (Fin j.val → ZMod 2) → (P n →ₗ[ZMod 2] ZMod 2))
    (ans : P n → Fin q → ZMod 2) (decode : (Fin q → ZMod 2) → Bool),
    (∀ (p : P n) (j : Fin q), ans p j =
      ask j (fun earlier => ans p ⟨earlier.val, Nat.lt_trans earlier.isLt j.isLt⟩) p) ∧
    (∀ b : ZMod 2, decode (ans (b,0)) = false) ∧
    (∀ x : V n, x ≠ 0 → decode (ans (c x, x)) = true)

def Good (n s : ℕ) (c : V n → ZMod 2) : Prop :=
  ∃ (h : V n →ₗ[ZMod 2] ZMod 2) (U U' : Submodule (ZMod 2) (V n)),
    s ≤ finrank (ZMod 2) U ∧ s ≤ finrank (ZMod 2) U' ∧
    (∀ x ∈ U, x ≠ 0 → c x = h x + 1) ∧ (∀ x ∈ U', x ≠ 0 → c x = h x)

lemma transcript_eq {n q : ℕ}
    (ask : (j : Fin q) → (Fin j.val → ZMod 2) → (P n →ₗ[ZMod 2] ZMod 2))
    (ans : P n → Fin q → ZMod 2)
    (hrec : ∀ (p : P n) (j : Fin q), ans p j =
      ask j (fun earlier => ans p ⟨earlier.val, Nat.lt_trans earlier.isLt j.isLt⟩) p)
    (p0 p : P n)
    (hp : ∀ j, ask j (fun earlier => ans p0 ⟨earlier.val, Nat.lt_trans earlier.isLt j.isLt⟩) p =
       ask j (fun earlier => ans p0 ⟨earlier.val, Nat.lt_trans earlier.isLt j.isLt⟩) p0) :
    ans p = ans p0 := by
  have key : ∀ m, ∀ j : Fin q, j.val < m → ans p j = ans p0 j := by
    intro m
    induction m with
    | zero => intro j hj; omega
    | succ m ih =>
      intro j hj
      have hpre : (fun earlier : Fin j.val => ans p ⟨earlier.val, Nat.lt_trans earlier.isLt j.isLt⟩) =
          (fun earlier => ans p0 ⟨earlier.val, Nat.lt_trans earlier.isLt j.isLt⟩) := by
        funext e; exact ih _ (by show e.val < m; have := e.isLt; omega)
      rw [hrec p j, hpre, hp j, ← hrec p0 j]
  funext j; exact key (j.val+1) j (by omega)

lemma zero_add_P {n : ℕ} (p : P n) : ((0 : ZMod 2), (0 : V n)) + p = p := by
  ext <;> simp

lemma finrank_P (n : ℕ) : finrank (ZMod 2) (P n) = n + 1 := by
  rw [Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun]; ring

lemma ker_big {n q : ℕ} (L : P n →ₗ[ZMod 2] (Fin q → ZMod 2)) :
    n + 1 ≤ finrank (ZMod 2) (LinearMap.ker L) + q := by
  have h1 := LinearMap.finrank_range_add_finrank_ker L
  have h2 : finrank (ZMod 2) (LinearMap.range L) ≤ q := by
    have := Submodule.finrank_le (LinearMap.range L); rwa [Module.finrank_fin_fun] at this
  rw [finrank_P] at h1; omega

lemma lower {n q : ℕ} (c : V n → ZMod 2) (hs : Succ n q c) :
    n ≤ q ∨ Good n (n+1-q) c := by
  classical
  obtain ⟨ask, ans, decode, hrec, hneg, hpos⟩ := hs
  have h00 : ∀ j, ans (0,0) j = 0 := by intro j; rw [hrec]; exact map_zero _
  let Lof : P n → P n →ₗ[ZMod 2] (Fin q → ZMod 2) := fun p0 =>
    LinearMap.pi (fun j => ask j (fun earlier => ans p0 ⟨earlier.val, Nat.lt_trans earlier.isLt j.isLt⟩))
  have hfib : ∀ p0 p, p ∈ LinearMap.ker (Lof p0) → ans (p0 + p) = ans p0 := by
    intro p0 p hp
    apply transcript_eq ask ans hrec
    intro j
    have : (Lof p0) p j = 0 := by rw [LinearMap.mem_ker.mp hp]; rfl
    rw [map_add]; simp only [Lof, LinearMap.pi_apply] at this; rw [this, add_zero]
  by_cases hz : ∀ j, ans (1,0) j = 0
  · left
    have hsame : ans (1,0) = ans (0,0) := by funext j; rw [hz, h00]
    have h10 : ((1 : ZMod 2), (0 : V n)) ∈ LinearMap.ker (Lof (0,0)) := by
      rw [LinearMap.mem_ker]; funext j
      simp only [Lof, LinearMap.pi_apply]
      rw [← hsame, ← hrec]; exact hz j
    have hsub : LinearMap.ker (Lof (0,0)) ≤ LinearMap.range (LinearMap.inl (ZMod 2) (ZMod 2) (V n)) := by
      intro p hp
      have hp2 : p.2 = 0 := by
        by_contra hx
        have e0 := hfib (0,0) p hp
        have e1 := hfib (0,0) ((1,0) + p) (Submodule.add_mem _ h10 hp)
        rw [zero_add_P] at e0
        rcases z2 (p.1 + c p.2) with h | h
        · have : (c p.2, p.2) = p := by
            refine Prod.ext ?_ ?_
            · show c p.2 = p.1
              have := h; revert this; generalize c p.2 = a; generalize p.1 = b; revert a b; decide
            · rfl
          have hp1 := hpos p.2 hx; rw [this, e0, hneg] at hp1; exact Bool.false_ne_true hp1
        · have : (c p.2, p.2) = (0,0) + ((1,0) + p) := by
            refine Prod.ext ?_ ?_
            · show c p.2 = 0 + (1 + p.1)
              have := h; revert this; generalize c p.2 = a; generalize p.1 = b; revert a b; decide
            · show p.2 = 0 + (0 + p.2); simp
          have hp1 := hpos p.2 hx; rw [this, e1, hneg] at hp1; exact Bool.false_ne_true hp1
      exact ⟨p.1, by ext <;> simp [hp2]⟩
    have hr : finrank (ZMod 2) (LinearMap.range (LinearMap.inl (ZMod 2) (ZMod 2) (V n))) = 1 := by
      rw [LinearMap.finrank_range_of_inj LinearMap.inl_injective, Module.finrank_self]
    have hm := Submodule.finrank_mono hsub
    rw [hr] at hm
    have := ker_big (Lof (0,0))
    omega
  · right
    push Not at hz
    have hex : ∃ m, ∃ hm : m < q, ans (1,0) ⟨m, hm⟩ ≠ 0 := by
      obtain ⟨j, hj⟩ := hz; exact ⟨j.val, j.isLt, hj⟩
    obtain ⟨hk, hk1⟩ := Nat.find_spec hex
    set k := Nat.find hex
    have hmin : ∀ m (hm : m < k), ans (1,0) ⟨m, by omega⟩ = 0 := by
      intro m hm
      have := Nat.find_min hex hm
      push Not at this
      exact this _
    let kk : Fin q := ⟨k, hk⟩
    let ℓ := ask kk (fun e => ans (0,0) ⟨e.val, Nat.lt_trans e.isLt kk.isLt⟩)
    have hℓ1 : ask kk (fun e => ans (1,0) ⟨e.val, Nat.lt_trans e.isLt kk.isLt⟩) = ℓ := by
      have : (fun e : Fin kk.val => ans (1,0) ⟨e.val, Nat.lt_trans e.isLt kk.isLt⟩) =
          (fun e => ans (0,0) ⟨e.val, Nat.lt_trans e.isLt kk.isLt⟩) := by
        funext e; rw [h00]; exact hmin e.val e.isLt
      rw [this]
    have hℓ10 : ℓ (1,0) = 1 := by
      rw [← hℓ1, ← hrec]
      rcases z2 (ans (1,0) kk) with h | h
      · exact absurd h hk1
      · exact h
    let h : V n →ₗ[ZMod 2] ZMod 2 := ℓ.comp (LinearMap.inr (ZMod 2) (ZMod 2) (V n))
    have hsplit : ∀ p : P n, ℓ p = p.1 + h p.2 := by
      intro p
      have : p = p.1 • ((1 : ZMod 2), (0 : V n)) + LinearMap.inr (ZMod 2) (ZMod 2) (V n) p.2 := by
        ext <;> simp
      conv_lhs => rw [this]
      rw [map_add, map_smul, hℓ10, smul_eq_mul, mul_one]; rfl
    let g : V n →ₗ[ZMod 2] P n := LinearMap.prod h LinearMap.id
    have hg : ∀ p : P n, ℓ p = 0 → g p.2 = p := by
      intro p hp
      rw [hsplit] at hp
      ext
      · show h p.2 = p.1
        revert hp; generalize h p.2 = a; generalize p.1 = b; revert a b; decide
      · rfl
    have hℓL0 : ∀ p ∈ LinearMap.ker (Lof (0,0)), ℓ p = 0 := by
      intro p hp
      have := congrFun (LinearMap.mem_ker.mp hp) kk
      simpa [Lof] using this
    have hℓL1 : ∀ p ∈ LinearMap.ker (Lof (1,0)), ℓ p = 0 := by
      intro p hp
      have := congrFun (LinearMap.mem_ker.mp hp) kk
      simp only [Lof, LinearMap.pi_apply] at this
      rw [hℓ1] at this; simpa using this
    have hdim : ∀ W : Submodule (ZMod 2) (P n), (∀ p ∈ W, ℓ p = 0) →
        finrank (ZMod 2) W ≤ finrank (ZMod 2) (W.comap g) := by
      intro W hW
      have : W ≤ (W.comap g).map g := by
        intro p hp
        exact ⟨p.2, by show g p.2 ∈ W; rw [hg p (hW p hp)]; exact hp, hg p (hW p hp)⟩
      exact (Submodule.finrank_mono this).trans (Submodule.finrank_map_le _ _)
    refine ⟨h, (LinearMap.ker (Lof (0,0))).comap g, (LinearMap.ker (Lof (1,0))).comap g, ?_, ?_, ?_, ?_⟩
    · have := hdim _ hℓL0; have := ker_big (Lof (0,0)); omega
    · have := hdim _ hℓL1; have := ker_big (Lof (1,0)); omega
    · intro x hx hx0
      have e := hfib (0,0) (g x) hx
      rw [zero_add_P] at e
      have hp := hpos x hx0
      have hne : c x ≠ h x := by
        intro hc
        have : (c x, x) = g x := by
          refine Prod.ext ?_ ?_
          · exact hc
          · rfl
        rw [this, e, hneg] at hp; exact Bool.false_ne_true hp
      have key : ∀ a b : ZMod 2, a ≠ b → a = b + 1 := by decide
      exact key _ _ hne
    · intro x hx hx0
      have e := hfib (1,0) (g x) hx
      have hp := hpos x hx0
      have hne : c x ≠ h x + 1 := by
        intro hc
        have : (c x, x) = (1,0) + g x := by
          refine Prod.ext ?_ ?_
          · show c x = 1 + h x; rw [hc, add_comm]
          · show x = 0 + x; simp
        rw [this, e, hneg] at hp; exact Bool.false_ne_true hp
      have key : ∀ a b : ZMod 2, a ≠ b + 1 → a = b := by decide
      exact key _ _ hne

lemma upper_full {n q : ℕ} (c : V n → ZMod 2) (hq : n ≤ q) : Succ n q c := by
  classical
  refine ⟨fun j _ => if hj : j.val < n then
      (LinearMap.proj (⟨j.val, hj⟩ : Fin n)).comp (LinearMap.snd (ZMod 2) (ZMod 2) (V n)) else 0,
    fun p j => if hj : j.val < n then p.2 ⟨j.val, hj⟩ else 0,
    fun τ => decide (∃ j, τ j ≠ 0), ?_, ?_, ?_⟩
  · intro p j; by_cases hj : j.val < n <;> simp [hj]
  · intro b; simp
  · intro x hx
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    simp only [decide_eq_true_eq]
    exact ⟨⟨i.val, by omega⟩, by simpa using hi⟩

def co {n : ℕ} (r : ℕ) (A : V n →ₗ[ZMod 2] (Fin r → ZMod 2)) (i : ℕ) : P n →ₗ[ZMod 2] ZMod 2 :=
  if hi : i < r then (LinearMap.proj (⟨i, hi⟩ : Fin r)).comp (A.comp (LinearMap.snd (ZMod 2) (ZMod 2) (V n)))
  else 0

lemma co_zero {n r : ℕ} (A : V n →ₗ[ZMod 2] (Fin r → ZMod 2)) (i : ℕ) (b : ZMod 2) :
    co r A i (b, 0) = 0 := by
  unfold co; split_ifs <;> simp

lemma co_pos {n r : ℕ} (A : V n →ₗ[ZMod 2] (Fin r → ZMod 2)) (i : Fin r) (p : P n) :
    co r A i.val p = A p.2 i := by
  unfold co; rw [dite_cond_eq_true (eq_true i.isLt)]; rfl

lemma upper_tree {n q r0 r1 : ℕ} (c : V n → ZMod 2) (h : V n →ₗ[ZMod 2] ZMod 2)
    (A0 : V n →ₗ[ZMod 2] (Fin r0 → ZMod 2)) (A1 : V n →ₗ[ZMod 2] (Fin r1 → ZMod 2))
    (h0 : r0 + 1 ≤ q) (h1 : r1 + 1 ≤ q)
    (hA0 : ∀ x, x ≠ 0 → A0 x = 0 → c x = h x + 1) (hA1 : ∀ x, x ≠ 0 → A1 x = 0 → c x = h x) :
    Succ n q c := by
  classical
  let ℓ : P n →ₗ[ZMod 2] ZMod 2 :=
    LinearMap.fst (ZMod 2) (ZMod 2) (V n) + h.comp (LinearMap.snd (ZMod 2) (ZMod 2) (V n))
  refine ⟨fun j pre => if hj : j.val = 0 then ℓ else
      if pre ⟨0, Nat.pos_of_ne_zero hj⟩ = 0 then co r0 A0 (j.val - 1) else co r1 A1 (j.val - 1),
    fun p j => if j.val = 0 then ℓ p else if ℓ p = 0 then co r0 A0 (j.val - 1) p else co r1 A1 (j.val - 1) p,
    fun τ => decide (∃ j : Fin q, j.val ≠ 0 ∧ τ j ≠ 0), ?_, ?_, ?_⟩
  · intro p j
    by_cases hj : j.val = 0
    · simp [hj]
    · simp [hj]
      split_ifs <;> rfl
  · intro b
    simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro j hj
    simp [hj, co_zero]
  · intro x hx
    simp only [decide_eq_true_eq]
    by_cases hl : ℓ (c x, x) = 0
    · have hne : A0 x ≠ 0 := by
        intro hA
        have := hA0 x hx hA
        have hl' : c x + h x = 0 := hl
        rw [this] at hl'
        revert hl'; generalize h x = a; revert a; decide
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      refine ⟨⟨i.val + 1, by omega⟩, by simp, ?_⟩
      simp only [hl, ite_true, Nat.add_sub_cancel, add_eq_zero, one_ne_zero, and_false, ite_false]
      rw [co_pos A0 i]; exact hi
    · have hne : A1 x ≠ 0 := by
        intro hA
        have := hA1 x hx hA
        have hl' : ¬ (c x + h x = 0) := hl
        rw [this] at hl'
        revert hl'; generalize h x = a; revert a; decide
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      refine ⟨⟨i.val + 1, by omega⟩, by simp, ?_⟩
      simp only [hl, ite_false, Nat.add_sub_cancel, add_eq_zero, one_ne_zero, and_false]
      rw [co_pos A1 i]; exact hi

lemma quot_map {n q : ℕ} (U : Submodule (ZMod 2) (V n)) (hU : n + 1 - q ≤ finrank (ZMod 2) U)
    (hq : 1 ≤ q) :
    ∃ (r : ℕ) (A : V n →ₗ[ZMod 2] (Fin r → ZMod 2)), r + 1 ≤ q ∧ ∀ x, A x = 0 → x ∈ U := by
  refine ⟨finrank (ZMod 2) (V n ⧸ U),
    ((Module.finBasis (ZMod 2) (V n ⧸ U)).equivFun.toLinearMap).comp U.mkQ, ?_, ?_⟩
  · have := Submodule.finrank_quotient_add_finrank U
    have h2 := Submodule.finrank_le U
    rw [Module.finrank_fin_fun] at this h2; omega
  · intro x hx
    have h1 : U.mkQ x = 0 := by
      simpa using hx
    simpa using h1

lemma upper_good {n q : ℕ} (c : V n → ZMod 2) (hq : 1 ≤ q) (hg : Good n (n+1-q) c) :
    Succ n q c := by
  obtain ⟨h, U, U', hU, hU', hc, hc'⟩ := hg
  obtain ⟨r0, A0, h0, hA0⟩ := quot_map U hU hq
  obtain ⟨r1, A1, h1, hA1⟩ := quot_map U' hU' hq
  exact upper_tree c h A0 A1 h0 h1 (fun x hx hA => hc x (hA0 x hA) hx)
    (fun x hx hA => hc' x (hA1 x hA) hx)

def Good0 (n s : ℕ) (χ : V n → ZMod 2) : Prop :=
  ∃ (g : V n →ₗ[ZMod 2] ZMod 2) (U U' : Submodule (ZMod 2) (V n)),
    s ≤ finrank (ZMod 2) U ∧ s ≤ finrank (ZMod 2) U' ∧
    (∀ x ∈ U, x ≠ 0 → χ x = g x + 1) ∧ (∀ x ∈ U', x ≠ 0 → χ x = g x)

lemma good_iff {n s : ℕ} (tilt : V n →ₗ[ZMod 2] ZMod 2) (offset : ZMod 2) (χ : V n → ZMod 2) :
    Good n s (fun x => tilt x + offset + χ x) ↔ Good0 n s χ := by
  rcases z2 offset with ho | ho <;> subst ho
  · constructor
    · rintro ⟨h, U, U', hU, hU', hc, hc'⟩
      refine ⟨h - tilt, U, U', hU, hU', fun x hx hx0 => ?_, fun x hx hx0 => ?_⟩
      · have := hc x hx hx0; rw [LinearMap.sub_apply]; beta_reduce at this ⊢; revert this
        generalize χ x = a; generalize h x = b; generalize tilt x = d; revert a b d; decide
      · have := hc' x hx hx0; rw [LinearMap.sub_apply]; beta_reduce at this ⊢; revert this
        generalize χ x = a; generalize h x = b; generalize tilt x = d; revert a b d; decide
    · rintro ⟨h, U, U', hU, hU', hc, hc'⟩
      refine ⟨h + tilt, U, U', hU, hU', fun x hx hx0 => ?_, fun x hx hx0 => ?_⟩
      · have := hc x hx hx0; show _ = (h x + tilt x) + 1; beta_reduce at this ⊢; revert this
        generalize χ x = a; generalize h x = b; generalize tilt x = d; revert a b d; decide
      · have := hc' x hx hx0; show _ = (h x + tilt x); beta_reduce at this ⊢; revert this
        generalize χ x = a; generalize h x = b; generalize tilt x = d; revert a b d; decide
  · constructor
    · rintro ⟨h, U, U', hU, hU', hc, hc'⟩
      refine ⟨h - tilt, U', U, hU', hU, fun x hx hx0 => ?_, fun x hx hx0 => ?_⟩
      · have := hc' x hx hx0; rw [LinearMap.sub_apply]; beta_reduce at this ⊢; revert this
        generalize χ x = a; generalize h x = b; generalize tilt x = d; revert a b d; decide
      · have := hc x hx hx0; rw [LinearMap.sub_apply]; beta_reduce at this ⊢; revert this
        generalize χ x = a; generalize h x = b; generalize tilt x = d; revert a b d; decide
    · rintro ⟨h, U, U', hU, hU', hc, hc'⟩
      refine ⟨h + tilt, U', U, hU', hU, fun x hx hx0 => ?_, fun x hx hx0 => ?_⟩
      · have := hc' x hx hx0; show _ = (h x + tilt x) + 1; beta_reduce at this ⊢; revert this
        generalize χ x = a; generalize h x = b; generalize tilt x = d; revert a b d; decide
      · have := hc x hx hx0; show _ = (h x + tilt x); beta_reduce at this ⊢; revert this
        generalize χ x = a; generalize h x = b; generalize tilt x = d; revert a b d; decide

lemma finrank_V (n : ℕ) : finrank (ZMod 2) (V n) = n := Module.finrank_fin_fun _

lemma fr_le {n : ℕ} (W : Submodule (ZMod 2) (V n)) : finrank (ZMod 2) W ≤ n := by
  have := Submodule.finrank_le W; rwa [finrank_V] at this

lemma inf_big {n : ℕ} (A B : Submodule (ZMod 2) (V n)) :
    finrank (ZMod 2) A + finrank (ZMod 2) B ≤ n + finrank (ZMod 2) (A ⊓ B : Submodule (ZMod 2) (V n)) := by
  have := Submodule.finrank_sup_add_finrank_inf_eq A B
  have := fr_le (A ⊔ B)
  omega

lemma ker_fun {n : ℕ} (g : V n →ₗ[ZMod 2] ZMod 2) : n ≤ finrank (ZMod 2) (LinearMap.ker g) + 1 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker g
  have h2 := Submodule.finrank_le (LinearMap.range g)
  rw [Module.finrank_self] at h2
  rw [finrank_V] at h1; omega

lemma exists_other {n : ℕ} (W : Submodule (ZMod 2) (V n)) (hW : 2 ≤ finrank (ZMod 2) W)
    (k : V n) : ∃ y ∈ W, y ≠ 0 ∧ y ≠ k := by
  by_contra hcon
  push Not at hcon
  have hle : W ≤ Submodule.span (ZMod 2) {k} := by
    intro y hy
    by_cases h0 : y = 0
    · rw [h0]; exact Submodule.zero_mem _
    · rw [hcon y hy h0]; exact Submodule.mem_span_singleton_self k
  have := Submodule.finrank_mono hle
  have h2 := finrank_span_le_card (R := ZMod 2) ({k} : Set (V n))
  simp at h2
  omega

lemma exists_ne0 {n : ℕ} (W : Submodule (ZMod 2) (V n)) (hW : 1 ≤ finrank (ZMod 2) W) :
    ∃ y ∈ W, y ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have : W = ⊥ := by
    rw [eq_bot_iff]; intro y hy; rw [Submodule.mem_bot]; exact hcon y hy
  rw [this, finrank_bot] at hW; omega

lemma exists_out {n : ℕ} (W : Submodule (ZMod 2) (V n)) (hW : finrank (ZMod 2) W < n) :
    ∃ w, w ∉ W := by
  by_contra hcon
  push Not at hcon
  have : W = ⊤ := by rw [eq_top_iff]; intro y _; exact hcon y
  rw [this, finrank_top, finrank_V] at hW; omega

lemma exists_fun {n : ℕ} (W : Submodule (ZMod 2) (V n)) (w : V n) (hw : w ∉ W) :
    ∃ g : V n →ₗ[ZMod 2] ZMod 2, g w = 1 ∧ ∀ y ∈ W, g y = 0 := by
  obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hw inferInstance
  refine ⟨f, ?_, fun y hy => ?_⟩
  · rcases z2 (f w) with h | h
    · exact absurd h hf
    · exact h
  · have : f y ∈ W.map f := Submodule.mem_map_of_mem hy
    rw [hmap, Submodule.mem_bot] at this; exact this

lemma finrank_lt_sup {n : ℕ} (W : Submodule (ZMod 2) (V n)) (w : V n) (hw : w ∉ W) :
    finrank (ZMod 2) W + 1 ≤ finrank (ZMod 2) (W ⊔ Submodule.span (ZMod 2) {w} : Submodule (ZMod 2) (V n)) := by
  have : W < W ⊔ Submodule.span (ZMod 2) {w} := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro he
    apply hw
    rw [he]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self w)
  have := Submodule.finrank_lt_finrank_of_lt this
  omega

noncomputable def chi {n : ℕ} (K : Submodule (ZMod 2) (V n)) (center : V n) (x : V n) : ZMod 2 :=
  if @decide (x - center ∈ K) (Classical.propDecidable _) then (1 : ZMod 2) else 0

lemma chi_one {n : ℕ} {K : Submodule (ZMod 2) (V n)} {center x : V n} (h : x - center ∈ K) :
    chi K center x = 1 := by unfold chi; simp [h]

lemma chi_zero {n : ℕ} {K : Submodule (ZMod 2) (V n)} {center x : V n} (h : x - center ∉ K) :
    chi K center x = 0 := by unfold chi; simp [h]

lemma chi_one_iff {n : ℕ} {K : Submodule (ZMod 2) (V n)} {center x : V n} :
    chi K center x = 1 ↔ x - center ∈ K := by
  by_cases h : x - center ∈ K
  · simp [chi_one h, h]
  · rw [chi_zero h]; simp [h]

lemma ne_succ (a : ZMod 2) : a ≠ a + 1 := by revert a; decide

lemma lower_in {n s : ℕ} (K : Submodule (ZMod 2) (V n)) (center : V n) (hcK : center ∈ K)
    (hs : 2 ≤ s) (hg : Good0 n s (chi K center)) :
    2 * s ≤ n ∧ s + finrank (ZMod 2) K ≤ n ∧ s ≤ finrank (ZMod 2) K + 1 := by
  obtain ⟨g, U, U', hU, hU', hc, hc'⟩ := hg
  have hK : ∀ x, x - center ∈ K ↔ x ∈ K := fun x => Submodule.sub_mem_iff_left K hcK
  refine ⟨?_, ?_, ?_⟩
  · have hd : U ⊓ U' = ⊥ := by
      rw [eq_bot_iff]; intro x hx
      rw [Submodule.mem_inf] at hx
      rw [Submodule.mem_bot]
      by_contra h0
      have := hc x hx.1 h0
      rw [hc' x hx.2 h0] at this
      exact ne_succ _ this
    have := inf_big U U'
    rw [hd, finrank_bot] at this; omega
  · have hd : U' ⊓ K = ⊥ := by
      rw [eq_bot_iff]; intro x hx
      rw [Submodule.mem_inf] at hx
      rw [Submodule.mem_bot]
      by_contra h0
      obtain ⟨y, hyU, hy0, hyx⟩ := exists_other U' (by omega) x
      have hyx0 : y + x ≠ 0 := fun h => hyx (eq_of_add_v h)
      have e1 := hc' (y + x) (U'.add_mem hyU hx.1) hyx0
      have e2 := hc' y hyU hy0
      have e3 := hc' x hx.1 h0
      have hxx : chi K center x = 1 := chi_one ((hK x).mpr hx.2)
      have hyy : chi K center (y + x) = chi K center y := by
        have : y + x - center ∈ K ↔ y - center ∈ K := by
          rw [hK, hK]; exact Submodule.add_mem_iff_left K hx.2
        by_cases hy : y - center ∈ K
        · rw [chi_one hy, chi_one (this.mpr hy)]
        · rw [chi_zero hy, chi_zero (fun h => hy (this.mp h))]
      rw [hyy, e2, map_add, ← e3, hxx] at e1
      exact ne_succ _ e1
    have := inf_big U' K
    rw [hd, finrank_bot] at this; omega
  · have hle : U ⊓ LinearMap.ker g ≤ K := by
      intro x hx
      rw [Submodule.mem_inf, LinearMap.mem_ker] at hx
      by_cases h0 : x = 0
      · rw [h0]; exact K.zero_mem
      · have := hc x hx.1 h0
        rw [hx.2, zero_add, chi_one_iff, hK] at this
        exact this
    have := inf_big U (LinearMap.ker g)
    have := ker_fun g
    have := Submodule.finrank_mono hle
    omega

lemma lower_out {n s : ℕ} (K : Submodule (ZMod 2) (V n)) (center : V n) (hcK : center ∉ K)
    (hs : 2 ≤ s) (hg : Good0 n s (chi K center)) :
    s ≤ 2 ∧ finrank (ZMod 2) K + 2 ≤ n := by
  obtain ⟨g, U, U', hU, hU', hc, hc'⟩ := hg
  refine ⟨?_, ?_⟩
  · by_contra h3
    have h1 := inf_big U (LinearMap.ker g)
    have h2 := ker_fun g
    have h4 : 2 ≤ finrank (ZMod 2) (U ⊓ LinearMap.ker g : Submodule (ZMod 2) (V n)) := by omega
    obtain ⟨x, hx, hx0⟩ := exists_ne0 _ (by omega : 1 ≤ finrank (ZMod 2) (U ⊓ LinearMap.ker g : Submodule (ZMod 2) (V n)))
    obtain ⟨y, hy, hy0, hyx⟩ := exists_other _ h4 x
    have hxy0 : x + y ≠ 0 := fun h => hyx (eq_of_add_v h).symm
    have hxy := Submodule.add_mem _ hx hy
    have mem : ∀ z ∈ (U ⊓ LinearMap.ker g : Submodule (ZMod 2) (V n)), z ≠ 0 → z - center ∈ K := by
      intro z hz hz0
      rw [Submodule.mem_inf, LinearMap.mem_ker] at hz
      have := hc z hz.1 hz0
      rw [hz.2, zero_add, chi_one_iff] at this; exact this
    have := K.sub_mem (K.add_mem (mem x hx hx0) (mem y hy hy0)) (mem _ hxy hxy0)
    have e : x - center + (y - center) - (x + y - center) = -center := by abel
    rw [e, K.neg_mem_iff] at this
    exact hcK this
  · by_contra h3
    obtain ⟨x, hx, hx0⟩ := exists_ne0 U (by omega)
    obtain ⟨y, hy, hy0, hyx⟩ := exists_other U (by omega) x
    have hxy0 : x + y ≠ 0 := fun h => hyx (eq_of_add_v h).symm
    have hxy := U.add_mem hx hy
    have hout : ∀ z, z ∉ K → z - center ∈ K := by
      intro z hz
      have hfr := finrank_lt_sup K z hz
      have htop : K ⊔ Submodule.span (ZMod 2) {z} = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        have := fr_le (K ⊔ Submodule.span (ZMod 2) {z})
        rw [finrank_V]; omega
      have hc : center ∈ K ⊔ Submodule.span (ZMod 2) {z} := by rw [htop]; trivial
      obtain ⟨k, hk, w, hw, hkw⟩ := Submodule.mem_sup.mp hc
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rcases z2 t with ht | ht <;> subst ht
      · rw [zero_smul, add_zero] at hkw; exact absurd (hkw ▸ hk) hcK
      · rw [one_smul] at hkw
        have : z - center = -k := by rw [← hkw]; abel
        rw [this]; exact K.neg_mem hk
    have gin : ∀ z ∈ U, z ≠ 0 → z ∈ K → g z = 1 := by
      intro z hz hz0 hzK
      have h1 : z - center ∉ K := fun h => hcK (by
        have := K.sub_mem hzK h; rwa [sub_sub_cancel] at this)
      have := hc z hz hz0
      rw [chi_zero h1] at this
      revert this; generalize g z = a; revert a; decide
    have gout : ∀ z ∈ U, z ≠ 0 → z ∉ K → g z = 0 := by
      intro z hz hz0 hzK
      have := hc z hz hz0
      rw [chi_one (hout z hzK)] at this
      revert this; generalize g z = a; revert a; decide
    have hadd := map_add g x y
    by_cases hxK : x ∈ K <;> by_cases hyK : y ∈ K
    · rw [gin _ hxy hxy0 (K.add_mem hxK hyK), gin x hx hx0 hxK, gin y hy hy0 hyK] at hadd
      revert hadd; decide
    · rw [gout _ hxy hxy0 (fun h => hyK ((Submodule.add_mem_iff_right K hxK).mp h)),
        gin x hx hx0 hxK, gout y hy hy0 hyK] at hadd
      revert hadd; decide
    · rw [gout _ hxy hxy0 (fun h => hxK ((Submodule.add_mem_iff_left K hyK).mp h)),
        gout x hx hx0 hxK, gin y hy hy0 hyK] at hadd
      revert hadd; decide
    · have hsum : x + y ∈ K := by
        have := K.sub_mem (hout x hxK) (hout y hyK)
        have e : x + y = (x - center - (y - center)) + (y + y) := by abel
        rw [e, two_v, add_zero]; exact this
      rw [gin _ hxy hxy0 hsum, gout x hx hx0 hxK, gout y hy hy0 hyK] at hadd
      revert hadd; decide

lemma upper_in {n s : ℕ} (K : Submodule (ZMod 2) (V n)) (center : V n) (hcK : center ∈ K)
    (hs : 2 ≤ s) (h1 : 2 * s ≤ n) (h2 : s + finrank (ZMod 2) K ≤ n) (h3 : s ≤ finrank (ZMod 2) K + 1) :
    Good0 n s (chi K center) := by
  have hK : ∀ x, x - center ∈ K ↔ x ∈ K := fun x => Submodule.sub_mem_iff_left K hcK
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl K
  have hfr := Submodule.finrank_add_eq_of_isCompl hC
  rw [finrank_V] at hfr
  have hdis : ∀ x ∈ C, x ≠ 0 → x ∉ K := by
    intro x hxC hx0 hxK
    exact hx0 (Submodule.disjoint_def.mp hC.disjoint x hxK hxC)
  by_cases hsd : s ≤ finrank (ZMod 2) K
  · refine ⟨0, K, C, hsd, by omega, fun x hx _ => ?_, fun x hx hx0 => ?_⟩
    · rw [chi_one ((hK x).mpr hx)]; simp
    · rw [chi_zero (fun h => hdis x hx hx0 ((hK x).mp h))]; simp
  · obtain ⟨w, hw⟩ := exists_out K (by omega)
    obtain ⟨g, hgw, hgK⟩ := exists_fun K w hw
    refine ⟨g, K ⊔ Submodule.span (ZMod 2) {w}, C ⊓ LinearMap.ker g, ?_, ?_, ?_, ?_⟩
    · have := finrank_lt_sup K w hw; omega
    · have := inf_big C (LinearMap.ker g); have := ker_fun g; omega
    · intro x hx _
      obtain ⟨k, hk, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rcases z2 t with ht | ht <;> subst ht
      · rw [zero_smul, add_zero, chi_one ((hK k).mpr hk), hgK k hk]; decide
      · rw [one_smul]
        have : k + w - center ∉ K := by
          rw [hK]; intro h; exact hw ((Submodule.add_mem_iff_right K hk).mp h)
        rw [chi_zero this, map_add, hgK k hk, hgw]; decide
    · intro x hx hx0
      rw [Submodule.mem_inf, LinearMap.mem_ker] at hx
      rw [hx.2, chi_zero (fun h => hdis x hx.1 hx0 ((hK x).mp h))]

lemma upper_out {n : ℕ} (hn : 4 ≤ n) (K : Submodule (ZMod 2) (V n)) (center : V n) (hcK : center ∉ K)
    (h2 : finrank (ZMod 2) K + 2 ≤ n) : Good0 n 2 (chi K center) := by
  have ha0 : center ≠ 0 := fun h => hcK (h ▸ K.zero_mem)
  have hW : finrank (ZMod 2) (K ⊔ Submodule.span (ZMod 2) {center} : Submodule (ZMod 2) (V n)) < n := by
    have := Submodule.finrank_sup_add_finrank_inf_eq K (Submodule.span (ZMod 2) {center})
    rw [finrank_span_singleton ha0] at this
    omega
  obtain ⟨b, hb⟩ := exists_out _ hW
  obtain ⟨g, hgb, hgW⟩ := exists_fun _ b hb
  obtain ⟨g2, hg2a, hg2K⟩ := exists_fun K center hcK
  have hga : g center = 0 := hgW _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  refine ⟨g, Submodule.span (ZMod 2) {center} ⊔ Submodule.span (ZMod 2) {b},
    LinearMap.ker g ⊓ LinearMap.ker g2, ?_, ?_, ?_, ?_⟩
  · have hb' : b ∉ Submodule.span (ZMod 2) {center} := fun h => hb (Submodule.mem_sup_right h)
    have := finrank_lt_sup _ b hb'
    rw [finrank_span_singleton ha0] at this; omega
  · have := inf_big (LinearMap.ker g) (LinearMap.ker g2)
    have := ker_fun g; have := ker_fun g2; omega
  · intro x hx hx0
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hy
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hz
    rcases z2 t with ht | ht <;> subst ht
    · rcases z2 s with hs | hs <;> subst hs
      · simp at hx0
      · rw [zero_smul, add_zero, one_smul, chi_one (by rw [sub_self]; exact K.zero_mem), hga]; decide
    · have : s • center + (1 : ZMod 2) • b - center ∉ K := by
        intro h
        apply hb
        have e : b = (s • center + (1 : ZMod 2) • b - center) + ((1 : ZMod 2) - s) • center := by
          rw [one_smul, sub_smul, one_smul]; abel
        rw [e]
        exact Submodule.add_mem _ (Submodule.mem_sup_left h)
          (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
      rw [chi_zero this, map_add, map_smul, map_smul, hga, hgb]; simp; decide
  · intro x hx _
    rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker] at hx
    rw [hx.1]
    apply chi_zero
    intro h
    have := hg2K _ h
    rw [map_sub, hx.2, hg2a] at this
    revert this; decide

theorem main (n : ℕ) (hn : 4 ≤ n) (K : Submodule (ZMod 2) (V n)) (center : V n)
    (tilt : V n →ₗ[ZMod 2] ZMod 2) (offset : ZMod 2) (q : ℕ) :
    Succ n q (fun x => tilt x + offset + chi K center x) ↔
    (if @decide (center ∈ K) (Classical.propDecidable _) then
        n+1 - max 1 (min (n/2) (min (n - finrank (ZMod 2) K) (finrank (ZMod 2) K + 1)))
      else if 2 ≤ n - finrank (ZMod 2) K then n-1 else n) ≤ q := by
  have hdK := fr_le K
  constructor
  · intro hs
    rcases lower _ hs with hq | hg
    · split_ifs <;> omega
    · by_cases hnq : n ≤ q
      · split_ifs <;> omega
      rw [good_iff] at hg
      by_cases hc : center ∈ K
      · obtain ⟨a, b, c⟩ := lower_in K center hc (by omega) hg
        rw [if_pos (by simpa using hc)]
        omega
      · obtain ⟨a, b⟩ := lower_out K center hc (by omega) hg
        rw [if_neg (by simpa using hc), if_pos (by omega)]
        omega
  · intro hq
    by_cases hnq : n ≤ q
    · exact upper_full _ hnq
    by_cases hc : center ∈ K
    · rw [if_pos (by simpa using hc)] at hq
      apply upper_good _ (by omega)
      rw [good_iff]
      exact upper_in K center hc (by omega) (by omega) (by omega) (by omega)
    · rw [if_neg (by simpa using hc)] at hq
      split_ifs at hq with h2
      · apply upper_good _ (by omega)
        rw [good_iff, show n + 1 - q = 2 by omega]
        exact upper_out hn K center hc (by omega)
      · omega

end PEqualNP.Outside.L_lib_780_aux

theorem PEqualNP.Outside.L_lib_780 : ∀ (n : Nat), 4 ≤ n →
  let F := ZMod 2
  let V := Fin n → F
  let P := F × V
  ∀ (K : Submodule F V) (center : V) (tilt : V →ₗ[F] F) (offset : F) (q : Nat),
    let copyBit := fun x : V => tilt x + offset +
      (if @decide (x-center ∈ K) (Classical.propDecidable _) then (1 : F) else 0)
    let dim := Module.finrank F K
    let codim := n-dim
    let aligned := n+1 - max 1 (min (n/2) (min codim (dim+1)))
    let cost := if @decide (center ∈ K) (Classical.propDecidable _) then aligned
      else if 2 ≤ codim then n-1 else n
    let success := ∃ (ask : (j : Fin q) → (Fin j.val → F) → (P →ₗ[F] F))
        (ans : P → Fin q → F) (decode : (Fin q → F) → Bool),
      (∀ (p : P) (j : Fin q), ans p j =
        ask j (fun earlier => ans p ⟨earlier.val, Nat.lt_trans earlier.isLt j.isLt⟩) p) ∧
      (∀ b : F, decode (ans (b,0)) = false) ∧
      (∀ x : V, x ≠ 0 → decode (ans (copyBit x,x)) = true)
    Iff success (cost ≤ q) := by
  intro n hn F V P K center tilt offset q copyBit dim codim aligned cost success
  exact PEqualNP.Outside.L_lib_780_aux.main n hn K center tilt offset q
