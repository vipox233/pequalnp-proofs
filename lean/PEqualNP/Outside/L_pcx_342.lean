import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_pcx_341
import PEqualNP.Outside.L_pcx_203
import PEqualNP.Outside.L_pcx_204
import PEqualNP.ProofComplexity.L055

open PEqualNP.ProofComplexity PEqualNP.Expanders

namespace PEqualNP.Outside.L_pcx_342_aux

open PEqualNP.Outside.L_pcx_341_aux.GraphCounts in
theorem simulate341 (m n t k : ℕ) (hn : 2 ≤ n) (hm : n < m) (hk : 1 ≤ k)
    (π : List (LinKLine (GEdge (G m n t)))) (hπ : IsLinKRefutation k (funGraphPHP (G m n t)) π) :
    ∃ τ, IsLinKRefutation k (funGraphPHP (PEqualNP.Outside.L_pcx_341_aux.Seed.K m n)) τ ∧
      τ.length ≤ 2 * π.length + 16 * m * n * (m + n) := by
  obtain ⟨seed, hd, odd, rows, cols, len⟩ := PEqualNP.Outside.L_pcx_341_aux.Seed.prelude m n hn hm
  obtain ⟨τ, hτ, ht⟩ := PEqualNP.Outside.L_pcx_341_aux.Replay.simulate k (funGraphPHP (G m n t))
    (funGraphPHP (PEqualNP.Outside.L_pcx_341_aux.Seed.K m n))
    PEqualNP.Outside.L_pcx_341_aux.StretchModel.support
    PEqualNP.Outside.L_pcx_341_aux.StretchModel.offset hk seed hd
    (fun C hC => Or.inr (PEqualNP.Outside.L_pcx_341_aux.StretchModel.axiom_step (by omega) seed
      odd rows cols C hC)) π hπ
  exact ⟨τ, hτ, ht.trans (Nat.add_le_add_left len _)⟩

namespace Main

open PEqualNP.Outside.L_pcx_341_aux.GraphCounts

noncomputable def relG {P Q : Type} {a b : ℕ} (eP : Fin a ≃ P) (eQ : Fin b ≃ Q)
    (rel : P → Q → Bool) : BipGraph a b :=
  fun u => Finset.univ.filter (fun v => rel (eP u) (eQ v) = true)

abbrev EP (J : Bool → ℕ) := Σ c : Bool, Fin (J c)
abbrev U' (z t : ℕ) (J : Bool → ℕ) := U (z+1) z t ⊕ EP J
abbrev V' (z t : ℕ) (J : Bool → ℕ) := V (z+1) z t ⊕ EP J

noncomputable def rel' (z t : ℕ) (J : Bool → ℕ) (A : Bool → Fin (Fintype.card (L (z+1) z)))
    (B : Bool → Fin (Fintype.card (R (z+1) z))) : U' z t J → V' z t J → Bool :=
  Sum.elim
    (fun u => Sum.elim (fun v => adj (z+1) z t u v)
      (fun h => decide (u = Sum.inl (A h.1) ∧ h.2.val = 0)))
    (fun q => Sum.elim (fun v => decide (v = Sum.inl (B q.1) ∧ q.2.val + 1 = J q.1))
      (fun h => decide (q.1 = h.1 ∧ (q.2.val = h.2.val ∨ h.2.val = q.2.val + 1))))

theorem card_U' (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) :
    Fintype.card (U' z t J) = Fintype.card (V' z t J) + 1 := by
  have h := (counts (z+1) z t hz (by omega)).2.2.1
  simp only [U', V', Fintype.card_sum] at h ⊢
  omega

noncomputable def graph (z t : ℕ) (J : Bool → ℕ) (A : Bool → Fin (Fintype.card (L (z+1) z)))
    (B : Bool → Fin (Fintype.card (R (z+1) z))) (hz : 2 ≤ z) :
    BipGraph (Fintype.card (V' z t J) + 1) (Fintype.card (V' z t J)) :=
  relG ((finCongr (card_U' z t J hz).symm).trans (Fintype.equivFin _).symm)
    (Fintype.equivFin _).symm (rel' z t J A B)

noncomputable def attA (z : ℕ) (hz : 2 ≤ z) (c : Bool) : Fin (Fintype.card (L (z+1) z)) :=
  Fintype.equivFin _ (Sum.inr (⟨if c then 1 else 0, by split <;> omega⟩, ⟨0, by omega⟩))

noncomputable def attB (z : ℕ) (hz : 2 ≤ z) (c : Bool) : Fin (Fintype.card (R (z+1) z)) :=
  Fintype.equivFin _ (Sum.inr (⟨if c then 1 else 0, by split <;> omega⟩, ⟨0, by omega⟩))

section Transport
variable {P Q : Type} [Fintype P] [Fintype Q] [DecidableEq P] [DecidableEq Q]

theorem mem_relG {a b : ℕ} (eP : Fin a ≃ P) (eQ : Fin b ≃ Q) (rel : P → Q → Bool)
    (u : Fin a) (v : Fin b) : v ∈ relG eP eQ rel u ↔ rel (eP u) (eQ v) = true := by
  simp [relG]

theorem card_edges_relG {a b : ℕ} (eP : Fin a ≃ P) (eQ : Fin b ≃ Q) (rel : P → Q → Bool) :
    Fintype.card (GEdge (relG eP eQ rel)) = Fintype.card {x : P × Q // rel x.1 x.2 = true} :=
  Fintype.card_congr (Equiv.subtypeEquiv (eP.prodCongr eQ) (fun x => mem_relG eP eQ rel x.1 x.2))

theorem card_left_relG {a b : ℕ} (eP : Fin a ≃ P) (eQ : Fin b ≃ Q) (rel : P → Q → Bool)
    (u : Fin a) : (relG eP eQ rel u).card = Fintype.card {q : Q // rel (eP u) q = true} := by
  rw [← Fintype.card_coe]
  exact Fintype.card_congr (Equiv.subtypeEquiv eQ (fun v => mem_relG eP eQ rel u v))

theorem card_right_relG {a b : ℕ} (eP : Fin a ≃ P) (eQ : Fin b ≃ Q) (rel : P → Q → Bool)
    (v : Fin b) : (rightNbrs (relG eP eQ rel) v).card =
      Fintype.card {p : P // rel p (eQ v) = true} := by
  rw [← Fintype.card_coe]
  refine Fintype.card_congr (Equiv.subtypeEquiv eP (fun u => ?_))
  simp only [rightNbrs, Finset.mem_filter, Finset.mem_univ, true_and]
  exact mem_relG eP eQ rel u v

theorem conn_relG {a b : ℕ} (eP : Fin a ≃ P) (eQ : Fin b ≃ Q) (rel : P → Q → Bool)
    (h : ∀ col : P ⊕ Q → Bool, (∀ p q, rel p q = true → col (Sum.inl p) = col (Sum.inr q)) →
      ∀ x y, col x = col y) :
    ∀ color : Fin a ⊕ Fin b → Bool, (∀ u, ∀ v ∈ relG eP eQ rel u,
      color (Sum.inl u) = color (Sum.inr v)) → ∀ x y, color x = color y := by
  intro color hc x y
  have key := h (fun w => color (Sum.map eP.symm eQ.symm w)) (by
    intro p q hpq
    have := hc (eP.symm p) (eQ.symm q) ((mem_relG eP eQ rel _ _).mpr (by simpa using hpq))
    simpa using this)
  have hx := key (Sum.map eP eQ x) (Sum.map eP eQ y)
  rcases x with x | x <;> rcases y with y | y <;> simpa using hx

theorem cycle_relG {a b : ℕ} (eP : Fin a ≃ P) (eQ : Fin b ≃ Q) (rel : P → Q → Bool) (s : ℕ)
    (us : Fin (s+2) ↪ Fin a) (vs : Fin (s+2) ↪ Fin b)
    (h : ∀ i, vs i ∈ relG eP eQ rel (us i) ∧ vs i ∈ relG eP eQ rel (us (i+1))) :
    ∃ (us' : Fin (s+2) ↪ P) (vs' : Fin (s+2) ↪ Q),
      ∀ i, rel (us' i) (vs' i) = true ∧ rel (us' (i+1)) (vs' i) = true :=
  ⟨us.trans eP.toEmbedding, vs.trans eQ.toEmbedding,
    fun i => ⟨(mem_relG eP eQ rel _ _).mp (h i).1, (mem_relG eP eQ rel _ _).mp (h i).2⟩⟩

end Transport

noncomputable abbrev eU (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) :
    Fin (Fintype.card (V' z t J) + 1) ≃ U' z t J :=
  (finCongr (card_U' z t J hz).symm).trans (Fintype.equivFin _).symm

noncomputable abbrev eV (z t : ℕ) (J : Bool → ℕ) : Fin (Fintype.card (V' z t J)) ≃ V' z t J :=
  (Fintype.equivFin _).symm


theorem ep_ext {J : Bool → ℕ} {x y : EP J} (h1 : x.1 = y.1) (h2 : x.2.val = y.2.val) : x = y := by
  rcases x with ⟨c, i⟩
  rcases y with ⟨c', i'⟩
  simp only at h1
  subst h1
  simp only at h2
  rw [Fin.ext h2]

theorem card_le_two_of {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P]
    (a b : α) (h : ∀ x, P x → x = a ∨ x = b) : Fintype.card {x // P x} ≤ 2 := by
  classical
  rw [Fintype.card_subtype]
  calc (Finset.univ.filter P).card ≤ ({a, b} : Finset α).card := Finset.card_le_card (by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        rcases h x hx with rfl | rfl <;> simp)
    _ ≤ 2 := Finset.card_le_two

theorem card_le_one_of {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P]
    (h : ∀ x y, P x → P y → x = y) : Fintype.card {x // P x} ≤ 1 :=
  Fintype.card_le_one_iff.mpr (fun a b => Subtype.ext (h a.1 b.1 a.2 b.2))

theorem card_zero_of {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P]
    (h : ∀ x, ¬ P x) : Fintype.card {x // P x} = 0 :=
  Fintype.card_eq_zero_iff.mpr ⟨fun x => h x.1 x.2⟩

theorem two_le_card_of {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P]
    (a b : α) (ha : P a) (hb : P b) (hab : a ≠ b) : 2 ≤ Fintype.card {x // P x} :=
  Fintype.one_lt_card_iff.mpr ⟨⟨a, ha⟩, ⟨b, hb⟩, fun h => hab (congrArg Subtype.val h)⟩

theorem card_sum_split {A B : Type} [Fintype A] [Fintype B] (P : A ⊕ B → Prop)
    [DecidablePred P] : Fintype.card {x // P x} =
      Fintype.card {a // P (Sum.inl a)} + Fintype.card {b // P (Sum.inr b)} := by
  simpa only [Fintype.card_sum] using Fintype.card_congr (Equiv.subtypeSum (p := P))

theorem H_mem (z : ℕ) (u : Fin (Fintype.card (L (z+1) z))) (v : Fin (Fintype.card (R (z+1) z))) :
    v ∈ H (z+1) z u ↔
      baseAdj (z+1) z ((Fintype.equivFin _).symm u) ((Fintype.equivFin _).symm v) = true := by
  simp only [H, Finset.mem_filter, Finset.mem_univ, true_and]

section Paths

noncomputable def tpg (z t : ℕ) (J : Bool → ℕ) (e : E (z+1) z) (j : ℕ) : U' z t J :=
  if h : j < t then Sum.inl (Sum.inr (e, ⟨j, h⟩)) else Sum.inl (Sum.inl e.val.1)

noncomputable def thl (z t : ℕ) (J : Bool → ℕ) (e : E (z+1) z) (j : ℕ) : V' z t J :=
  if h : j < t then Sum.inl (Sum.inr (e, ⟨j, h⟩)) else Sum.inl (Sum.inl e.val.2)

noncomputable def epg (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) (c : Bool) (j : ℕ) : U' z t J :=
  if h : j < J c then Sum.inr ⟨c, ⟨j, h⟩⟩ else Sum.inl (Sum.inl (attA z hz c))

noncomputable def ehl (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) (c : Bool) (j : ℕ) : V' z t J :=
  if h : j < J c then Sum.inr ⟨c, ⟨j, h⟩⟩ else Sum.inl (Sum.inl (attB z hz c))

theorem tpg_fin (z t : ℕ) (J : Bool → ℕ) (e : E (z+1) z) (j : Fin t) :
    tpg z t J e j.val = Sum.inl (Sum.inr (e, j)) := by
  simp [tpg]

theorem thl_fin (z t : ℕ) (J : Bool → ℕ) (e : E (z+1) z) (j : Fin t) :
    thl z t J e j.val = Sum.inl (Sum.inr (e, j)) := by
  simp [thl]

theorem epg_fin (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) (q : EP J) :
    epg z t J hz q.1 q.2.val = Sum.inr q := by
  simp [epg]

theorem ehl_fin (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) (q : EP J) :
    ehl z t J hz q.1 q.2.val = Sum.inr q := by
  simp [ehl]

theorem t_np (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) (e : E (z+1) z) :
    ∀ j < t, ∀ y, rel' z t J (attA z hz) (attB z hz) (tpg z t J e j) y = true →
      y = thl z t J e j ∨ y = (if j + 1 < t then thl z t J e (j + 1) else Sum.inl (Sum.inl e.val.2)) := by
  intro j hj y hy
  simp only [tpg, dif_pos hj] at hy
  rcases y with (v | ⟨e', j'⟩) | q
  · simp only [rel', Sum.elim_inl, adj, Sum.elim_inr, decide_eq_true_eq] at hy
    obtain ⟨rfl, hjt⟩ := hy
    right
    rw [if_neg (by omega)]
  · simp only [rel', Sum.elim_inl, adj, Sum.elim_inr, decide_eq_true_eq] at hy
    obtain ⟨rfl, hj' | hj'⟩ := hy
    · left
      simp only [thl, dif_pos hj, ← hj']
    · right
      have h1 : j + 1 < t := by have := j'.isLt; omega
      rw [if_pos h1]
      simp only [thl, dif_pos h1, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq, true_and]
      exact Fin.ext hj'
  · simp [rel'] at hy

theorem t_nh (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) (e : E (z+1) z) :
    ∀ j < t, ∀ x, rel' z t J (attA z hz) (attB z hz) x (thl z t J e j) = true →
      x = tpg z t J e j ∨ x = (if j = 0 then Sum.inl (Sum.inl e.val.1) else tpg z t J e (j - 1)) := by
  intro j hj x hx
  simp only [thl, dif_pos hj] at hx
  rcases x with (u | ⟨e', j'⟩) | q
  · simp only [rel', Sum.elim_inl, adj, Sum.elim_inr, decide_eq_true_eq] at hx
    obtain ⟨rfl, hj0⟩ := hx
    right
    rw [if_pos hj0]
  · simp only [rel', Sum.elim_inl, adj, Sum.elim_inr, decide_eq_true_eq] at hx
    obtain ⟨rfl, hj' | hj'⟩ := hx
    · left
      simp only [tpg, dif_pos hj, hj']
    · right
      rw [if_neg (by omega)]
      have h1 : j - 1 < t := by omega
      simp only [tpg, dif_pos h1, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq, true_and]
      exact Fin.ext (by simp only; omega)
  · simp [rel'] at hx

theorem e_np (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) (c : Bool) :
    ∀ j < J c, ∀ y, rel' z t J (attA z hz) (attB z hz) (epg z t J hz c j) y = true →
      y = ehl z t J hz c j ∨
        y = (if j + 1 < J c then ehl z t J hz c (j + 1) else Sum.inl (Sum.inl (attB z hz c))) := by
  intro j hj y hy
  simp only [epg, dif_pos hj] at hy
  rcases y with v | ⟨c', j'⟩
  · simp only [rel', Sum.elim_inl, Sum.elim_inr, decide_eq_true_eq] at hy
    obtain ⟨rfl, hjt⟩ := hy
    right
    rw [if_neg (by omega)]
  · simp only [rel', Sum.elim_inr, decide_eq_true_eq] at hy
    obtain ⟨hc, hj' | hj'⟩ := hy
    · subst hc
      left
      simp only [ehl, dif_pos hj]
      exact congrArg Sum.inr (ep_ext rfl hj'.symm)
    · subst hc
      right
      have h1 : j + 1 < J c := by have := j'.isLt; omega
      rw [if_pos h1]
      simp only [ehl, dif_pos h1]
      exact congrArg Sum.inr (ep_ext rfl hj')

theorem e_nh (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) (c : Bool) :
    ∀ j < J c, ∀ x, rel' z t J (attA z hz) (attB z hz) x (ehl z t J hz c j) = true →
      x = epg z t J hz c j ∨
        x = (if j = 0 then Sum.inl (Sum.inl (attA z hz c)) else epg z t J hz c (j - 1)) := by
  intro j hj x hx
  simp only [ehl, dif_pos hj] at hx
  rcases x with u | ⟨c', j'⟩
  · simp only [rel', Sum.elim_inl, Sum.elim_inr, decide_eq_true_eq] at hx
    obtain ⟨rfl, hj0⟩ := hx
    right
    rw [if_pos (by simpa using hj0)]
  · simp only [rel', Sum.elim_inr, decide_eq_true_eq] at hx
    obtain ⟨hc, hj' | hj'⟩ := hx
    · subst hc
      left
      simp only [epg, dif_pos hj]
      exact congrArg Sum.inr (ep_ext rfl hj')
    · subst hc
      right
      rw [if_neg (by omega)]
      have h1 : j - 1 < J c' := by omega
      simp only [epg, dif_pos h1]
      exact congrArg Sum.inr (ep_ext rfl (by simp only; omega))

theorem t_np_in (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) (e : E (z+1) z) (j : ℕ) (hj : j < t) :
    rel' z t J (attA z hz) (attB z hz) (tpg z t J e j) (thl z t J e j) = true ∧
    rel' z t J (attA z hz) (attB z hz) (tpg z t J e j)
      (if j + 1 < t then thl z t J e (j + 1) else Sum.inl (Sum.inl e.val.2)) = true ∧
    thl z t J e j ≠ (if j + 1 < t then thl z t J e (j + 1) else Sum.inl (Sum.inl e.val.2)) := by
  by_cases h1 : j + 1 < t
  · simp only [if_pos h1, tpg, thl, dif_pos hj, dif_pos h1]
    refine ⟨by simp [rel', adj], by simp [rel', adj], ?_⟩
    simp [Fin.ext_iff]
  · simp only [if_neg h1, tpg, thl, dif_pos hj]
    refine ⟨by simp [rel', adj], ?_, by simp⟩
    simp [rel', adj] <;> omega

theorem t_nh_in (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) (e : E (z+1) z) (j : ℕ) (hj : j < t) :
    rel' z t J (attA z hz) (attB z hz) (tpg z t J e j) (thl z t J e j) = true ∧
    rel' z t J (attA z hz) (attB z hz)
      (if j = 0 then Sum.inl (Sum.inl e.val.1) else tpg z t J e (j - 1)) (thl z t J e j) = true ∧
    tpg z t J e j ≠ (if j = 0 then Sum.inl (Sum.inl e.val.1) else tpg z t J e (j - 1)) := by
  by_cases h1 : j = 0
  · subst h1
    simp only [if_pos rfl, tpg, thl, dif_pos hj]
    exact ⟨by simp [rel', adj], by simp [rel', adj], by simp⟩
  · have h2 : j - 1 < t := by omega
    simp only [if_neg h1, tpg, thl, dif_pos hj, dif_pos h2]
    refine ⟨by simp [rel', adj], ?_, ?_⟩
    · simp [rel', adj] <;> omega
    · simp [Fin.ext_iff] <;> omega

theorem e_np_in (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) (c : Bool) (j : ℕ) (hj : j < J c) :
    rel' z t J (attA z hz) (attB z hz) (epg z t J hz c j) (ehl z t J hz c j) = true ∧
    rel' z t J (attA z hz) (attB z hz) (epg z t J hz c j)
      (if j + 1 < J c then ehl z t J hz c (j + 1) else Sum.inl (Sum.inl (attB z hz c))) = true ∧
    ehl z t J hz c j ≠
      (if j + 1 < J c then ehl z t J hz c (j + 1) else Sum.inl (Sum.inl (attB z hz c))) := by
  by_cases h1 : j + 1 < J c
  · simp only [if_pos h1, epg, ehl, dif_pos hj, dif_pos h1]
    refine ⟨by simp [rel'], by simp [rel'], ?_⟩
    intro h
    have := congrArg (fun x : V' z t J => Sum.elim (fun _ => 0) (fun q : EP J => q.2.val) x) h
    simp at this
  · simp only [if_neg h1, epg, ehl, dif_pos hj]
    refine ⟨by simp [rel'], ?_, by simp⟩
    simp [rel'] <;> omega

theorem e_nh_in (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) (c : Bool) (j : ℕ) (hj : j < J c) :
    rel' z t J (attA z hz) (attB z hz) (epg z t J hz c j) (ehl z t J hz c j) = true ∧
    rel' z t J (attA z hz) (attB z hz)
      (if j = 0 then Sum.inl (Sum.inl (attA z hz c)) else epg z t J hz c (j - 1))
      (ehl z t J hz c j) = true ∧
    epg z t J hz c j ≠
      (if j = 0 then Sum.inl (Sum.inl (attA z hz c)) else epg z t J hz c (j - 1)) := by
  by_cases h1 : j = 0
  · subst h1
    simp only [if_pos rfl, epg, ehl, dif_pos hj]
    exact ⟨by simp [rel'], by simp [rel'], by simp⟩
  · have h2 : j - 1 < J c := by omega
    simp only [if_neg h1, epg, ehl, dif_pos hj, dif_pos h2]
    refine ⟨by simp [rel'], ?_, ?_⟩
    · simp [rel'] <;> omega
    · intro h
      have := congrArg (fun x : U' z t J => Sum.elim (fun _ => 0) (fun q : EP J => q.2.val) x) h
      simp only [Sum.elim_inr] at this
      omega

end Paths

section Degrees

theorem two_of_path {α : Type} [Fintype α] (P : α → Prop) [DecidablePred P] (a b : α)
    (hn : ∀ x, P x → x = a ∨ x = b) (ha : P a) (hb : P b) (hab : a ≠ b) :
    2 ≤ Fintype.card {x // P x} ∧ Fintype.card {x // P x} ≤ 3 :=
  ⟨two_le_card_of P a b ha hb hab, (card_le_two_of P a b hn).trans (by norm_num)⟩

theorem old_nbr_L (z t : ℕ) (ht : 1 ≤ t) (x : Fin (Fintype.card (L (z+1) z))) (a : V (z+1) z t)
    (h : adj (z+1) z t (Sum.inl x) a = true) :
    ∃ e : E (z+1) z, ∃ j : Fin t, a = Sum.inr (e, j) ∧ e.val.1 = x ∧ j.val = 0 := by
  rcases a with w | ⟨e, j⟩
  · simp only [adj, Sum.elim_inl, decide_eq_true_eq] at h
    exact absurd h.1 (by omega)
  · simp only [adj, Sum.elim_inl, Sum.elim_inr, decide_eq_true_eq] at h
    exact ⟨e, j, rfl, h.1.symm, h.2⟩

theorem old_nbr_R (z t : ℕ) (ht : 1 ≤ t) (y : Fin (Fintype.card (R (z+1) z))) (a : U (z+1) z t)
    (h : adj (z+1) z t a (Sum.inl y) = true) :
    ∃ e : E (z+1) z, ∃ j : Fin t, a = Sum.inr (e, j) ∧ e.val.2 = y ∧ j.val + 1 = t := by
  rcases a with w | ⟨e, j⟩
  · simp only [adj, Sum.elim_inl, decide_eq_true_eq] at h
    exact absurd h.1 (by omega)
  · simp only [adj, Sum.elim_inl, Sum.elim_inr, decide_eq_true_eq] at h
    exact ⟨e, j, rfl, h.1.symm, h.2⟩

theorem old_left_le (z t : ℕ) (ht : 1 ≤ t) (x : Fin (Fintype.card (L (z+1) z))) :
    Fintype.card {a : V (z+1) z t // adj (z+1) z t (Sum.inl x) a = true} ≤
      Fintype.card {y : R (z+1) z // baseAdj (z+1) z ((Fintype.equivFin _).symm x) y = true} := by
  refine Fintype.card_le_of_injective (fun a => ⟨(Fintype.equivFin (R (z+1) z)).symm
    (Sum.elim id (fun s : E (z+1) z × Fin t => s.1.val.2) a.1), ?_⟩) ?_
  · obtain ⟨e, j, ha, he1, -⟩ := old_nbr_L z t ht x a.1 a.2
    rw [ha]
    simp only [Sum.elim_inr]
    rw [← he1]
    exact (H_mem z _ _).mp e.2
  · intro a a' hh
    obtain ⟨e, j, ha, he1, hj⟩ := old_nbr_L z t ht x a.1 a.2
    obtain ⟨e', j', ha', he1', hj'⟩ := old_nbr_L z t ht x a'.1 a'.2
    have h2 := (Fintype.equivFin (R (z+1) z)).symm.injective (congrArg Subtype.val hh)
    rw [ha, ha'] at h2
    simp only [Sum.elim_inr] at h2
    apply Subtype.ext
    rw [ha, ha']
    have : e = e' := Subtype.ext (Prod.ext (he1.trans he1'.symm) h2)
    rw [this, Fin.ext (hj.trans hj'.symm)]

theorem old_right_le (z t : ℕ) (ht : 1 ≤ t) (y : Fin (Fintype.card (R (z+1) z))) :
    Fintype.card {a : U (z+1) z t // adj (z+1) z t a (Sum.inl y) = true} ≤
      Fintype.card {x : L (z+1) z // baseAdj (z+1) z x ((Fintype.equivFin _).symm y) = true} := by
  refine Fintype.card_le_of_injective (fun a => ⟨(Fintype.equivFin (L (z+1) z)).symm
    (Sum.elim id (fun s : E (z+1) z × Fin t => s.1.val.1) a.1), ?_⟩) ?_
  · obtain ⟨e, j, ha, he1, -⟩ := old_nbr_R z t ht y a.1 a.2
    rw [ha]
    simp only [Sum.elim_inr]
    rw [← he1]
    exact (H_mem z _ _).mp e.2
  · intro a a' hh
    obtain ⟨e, j, ha, he1, hj⟩ := old_nbr_R z t ht y a.1 a.2
    obtain ⟨e', j', ha', he1', hj'⟩ := old_nbr_R z t ht y a'.1 a'.2
    have h2 := (Fintype.equivFin (L (z+1) z)).symm.injective (congrArg Subtype.val hh)
    rw [ha, ha'] at h2
    simp only [Sum.elim_inr] at h2
    apply Subtype.ext
    rw [ha, ha']
    have : e = e' := Subtype.ext (Prod.ext h2 (he1.trans he1'.symm))
    rw [this, Fin.ext (show j.val = j'.val by omega)]

theorem old_left_ge (z t : ℕ) (ht : 1 ≤ t) (x : Fin (Fintype.card (L (z+1) z))) :
    Fintype.card {y : R (z+1) z // baseAdj (z+1) z ((Fintype.equivFin _).symm x) y = true} ≤
      Fintype.card {a : V (z+1) z t // adj (z+1) z t (Sum.inl x) a = true} := by
  refine Fintype.card_le_of_injective (fun y => ⟨Sum.inr (⟨(x, Fintype.equivFin _ y.1),
    (H_mem z _ _).mpr (by rw [Equiv.symm_apply_apply]; exact y.2)⟩, ⟨0, by omega⟩), by simp [adj]⟩) ?_
  refine Function.Injective.of_comp (f := fun a : {a : V (z+1) z t // adj (z+1) z t (Sum.inl x) a = true} =>
    (Fintype.equivFin (R (z+1) z)).symm (Sum.elim id (fun s : E (z+1) z × Fin t => s.1.val.2) a.1)) ?_
  intro y y' h
  apply Subtype.ext
  simpa using h

theorem old_right_ge (z t : ℕ) (ht : 1 ≤ t) (y : Fin (Fintype.card (R (z+1) z))) :
    Fintype.card {x : L (z+1) z // baseAdj (z+1) z x ((Fintype.equivFin _).symm y) = true} ≤
      Fintype.card {a : U (z+1) z t // adj (z+1) z t a (Sum.inl y) = true} := by
  refine Fintype.card_le_of_injective (fun x => ⟨Sum.inr (⟨(Fintype.equivFin _ x.1, y),
    (H_mem z _ _).mpr (by rw [Equiv.symm_apply_apply]; exact x.2)⟩, ⟨t - 1, by omega⟩),
    by simp [adj]; omega⟩) ?_
  refine Function.Injective.of_comp (f := fun a : {a : U (z+1) z t // adj (z+1) z t a (Sum.inl y) = true} =>
    (Fintype.equivFin (L (z+1) z)).symm (Sum.elim id (fun s : E (z+1) z × Fin t => s.1.val.1) a.1)) ?_
  intro x x' h
  apply Subtype.ext
  simpa using h

theorem baseL_ge2 (z : ℕ) (hz : 2 ≤ z) (x : L (z+1) z) :
    2 ≤ Fintype.card {y : R (z+1) z // baseAdj (z+1) z x y = true} := by
  rcases x with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ | ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  · by_cases hj' : j + 1 < z
    · exact two_le_card_of _ (Sum.inl (⟨i, hi⟩, ⟨j, hj⟩)) (Sum.inr (⟨i, hi⟩, ⟨j, by omega⟩))
        (by simp [baseAdj]) (by simp [baseAdj]) (by simp)
    · exact two_le_card_of _ (Sum.inl (⟨i, hi⟩, ⟨j, hj⟩)) (Sum.inr (⟨i, hi⟩, ⟨j - 1, by omega⟩))
        (by simp [baseAdj]) (by simp [baseAdj] <;> omega) (by simp)
  · exact two_le_card_of _ (Sum.inl (⟨i, by omega⟩, ⟨j, hj⟩)) (Sum.inl (⟨i + 1, by omega⟩, ⟨j, hj⟩))
      (by simp [baseAdj]) (by simp [baseAdj]) (by simp)

theorem baseR_ge2 (z : ℕ) (hz : 2 ≤ z) (y : R (z+1) z) :
    2 ≤ Fintype.card {x : L (z+1) z // baseAdj (z+1) z x y = true} := by
  rcases y with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ | ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
  · by_cases hi' : i < z
    · exact two_le_card_of _ (Sum.inl (⟨i, hi⟩, ⟨j, hj⟩)) (Sum.inr (⟨i, by omega⟩, ⟨j, hj⟩))
        (by simp [baseAdj]) (by simp [baseAdj]) (by simp)
    · exact two_le_card_of _ (Sum.inl (⟨i, hi⟩, ⟨j, hj⟩)) (Sum.inr (⟨i - 1, by omega⟩, ⟨j, hj⟩))
        (by simp [baseAdj]) (by simp [baseAdj] <;> omega) (by simp)
  · exact two_le_card_of _ (Sum.inl (⟨i, hi⟩, ⟨j, by omega⟩)) (Sum.inl (⟨i, hi⟩, ⟨j + 1, by omega⟩))
      (by simp [baseAdj]) (by simp [baseAdj]) (by simp)

theorem baseL_conn_le2 (z : ℕ) (s : Fin (z+1-1) × Fin z) :
    Fintype.card {y : R (z+1) z // baseAdj (z+1) z (Sum.inr s) y = true} ≤ 2 := by
  have hs := s.1.isLt
  apply card_le_two_of _ (Sum.inl (⟨s.1.val, by omega⟩, s.2))
    (Sum.inl (⟨s.1.val + 1, by omega⟩, s.2))
  rintro (⟨i, j⟩ | w) hy
  · simp only [baseAdj, Sum.elim_inl, Sum.elim_inr, decide_eq_true_eq] at hy
    obtain ⟨rfl, h | h⟩ := hy
    · left
      simp only [Sum.inl.injEq, Prod.mk.injEq, and_true]
      exact Fin.ext h
    · right
      simp only [Sum.inl.injEq, Prod.mk.injEq, and_true]
      exact Fin.ext h
  · simp [baseAdj] at hy

theorem baseR_conn_le2 (z : ℕ) (s : Fin (z+1) × Fin (z-1)) :
    Fintype.card {x : L (z+1) z // baseAdj (z+1) z x (Sum.inr s) = true} ≤ 2 := by
  have hs := s.2.isLt
  apply card_le_two_of _ (Sum.inl (s.1, ⟨s.2.val, by omega⟩))
    (Sum.inl (s.1, ⟨s.2.val + 1, by omega⟩))
  rintro (⟨i, j⟩ | w) hy
  · simp only [baseAdj, Sum.elim_inl, Sum.elim_inr, decide_eq_true_eq] at hy
    obtain ⟨rfl, h | h⟩ := hy
    · left
      simp only [Sum.inl.injEq, Prod.mk.injEq, true_and]
      exact Fin.ext h
    · right
      simp only [Sum.inl.injEq, Prod.mk.injEq, true_and]
      exact Fin.ext h
  · simp [baseAdj] at hy

theorem attA_symm (z : ℕ) (hz : 2 ≤ z) (c : Bool) :
    ∃ s, (Fintype.equivFin (L (z+1) z)).symm (attA z hz c) = Sum.inr s := by
  unfold attA
  exact ⟨_, Equiv.symm_apply_apply _ _⟩

theorem attB_symm (z : ℕ) (hz : 2 ≤ z) (c : Bool) :
    ∃ s, (Fintype.equivFin (R (z+1) z)).symm (attB z hz c) = Sum.inr s := by
  unfold attB
  exact ⟨_, Equiv.symm_apply_apply _ _⟩

theorem attA_inj (z : ℕ) (hz : 2 ≤ z) {c c' : Bool} (h : attA z hz c = attA z hz c') : c = c' := by
  have h1 := (Fintype.equivFin _).injective h
  have h2 := congrArg (fun x : L (z+1) z => Sum.elim (fun _ => 0) (fun s => s.1.val) x) h1
  cases c <;> cases c' <;> simp_all

theorem attB_inj (z : ℕ) (hz : 2 ≤ z) {c c' : Bool} (h : attB z hz c = attB z hz c') : c = c' := by
  have h1 := (Fintype.equivFin _).injective h
  have h2 := congrArg (fun x : R (z+1) z => Sum.elim (fun _ => 0) (fun s => s.1.val) x) h1
  cases c <;> cases c' <;> simp_all

theorem adj_deg_L_le3 (z t : ℕ) (hz : 2 ≤ z) (x : Fin (Fintype.card (L (z+1) z))) :
    Fintype.card {a : V (z+1) z t // adj (z+1) z t (Sum.inl x) a = true} ≤ 3 := by
  have hc := (counts (z+1) z t hz (by omega)).1 (Fintype.equivFin (U (z+1) z t) (Sum.inl x))
  have h := card_left_relG (Fintype.equivFin (U (z+1) z t)).symm
    (Fintype.equivFin (V (z+1) z t)).symm (adj (z+1) z t) (Fintype.equivFin (U (z+1) z t) (Sum.inl x))
  simp only [Equiv.symm_apply_apply] at h
  rw [← h]
  exact hc

theorem adj_deg_R_le3 (z t : ℕ) (hz : 2 ≤ z) (y : Fin (Fintype.card (R (z+1) z))) :
    Fintype.card {a : U (z+1) z t // adj (z+1) z t a (Sum.inl y) = true} ≤ 3 := by
  have hc := (counts (z+1) z t hz (by omega)).2.1 (Fintype.equivFin (V (z+1) z t) (Sum.inl y))
  have h := card_right_relG (Fintype.equivFin (U (z+1) z t)).symm
    (Fintype.equivFin (V (z+1) z t)).symm (adj (z+1) z t) (Fintype.equivFin (V (z+1) z t) (Sum.inl y))
  simp only [Equiv.symm_apply_apply] at h
  rw [← h]
  exact hc

theorem old_left_deg (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) (ht : 1 ≤ t)
    (x : Fin (Fintype.card (L (z+1) z))) :
    2 ≤ Fintype.card {q // rel' z t J (attA z hz) (attB z hz) (Sum.inl (Sum.inl x)) q = true} ∧
    Fintype.card {q // rel' z t J (attA z hz) (attB z hz) (Sum.inl (Sum.inl x)) q = true} ≤ 3 := by
  rw [card_sum_split]
  have h1 : Fintype.card {a : V (z+1) z t //
      rel' z t J (attA z hz) (attB z hz) (Sum.inl (Sum.inl x)) (Sum.inl a) = true} =
      Fintype.card {a : V (z+1) z t // adj (z+1) z t (Sum.inl x) a = true} := rfl
  rw [h1]
  have hge := (baseL_ge2 z hz _).trans (old_left_ge z t ht x)
  have hear : Fintype.card {h : EP J //
      rel' z t J (attA z hz) (attB z hz) (Sum.inl (Sum.inl x)) (Sum.inr h) = true} ≤ 1 := by
    apply card_le_one_of
    intro h h' hh hh'
    simp only [rel', Sum.elim_inl, Sum.elim_inr, decide_eq_true_eq, Sum.inl.injEq] at hh hh'
    exact ep_ext (attA_inj z hz (hh.1.symm.trans hh'.1)) (hh.2.trans hh'.2.symm)
  by_cases hA : ∃ c, x = attA z hz c
  · obtain ⟨c, rfl⟩ := hA
    obtain ⟨s, hs⟩ := attA_symm z hz c
    have hle := old_left_le z t ht (attA z hz c)
    rw [hs] at hle
    have hb := baseL_conn_le2 z s
    omega
  · have h0 : Fintype.card {h : EP J //
        rel' z t J (attA z hz) (attB z hz) (Sum.inl (Sum.inl x)) (Sum.inr h) = true} = 0 := by
      apply card_zero_of
      intro h hh
      simp only [rel', Sum.elim_inl, Sum.elim_inr, decide_eq_true_eq, Sum.inl.injEq] at hh
      exact hA ⟨h.1, hh.1⟩
    have := adj_deg_L_le3 z t hz x
    omega

theorem old_right_deg (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) (ht : 1 ≤ t)
    (y : Fin (Fintype.card (R (z+1) z))) :
    2 ≤ Fintype.card {p // rel' z t J (attA z hz) (attB z hz) p (Sum.inl (Sum.inl y)) = true} ∧
    Fintype.card {p // rel' z t J (attA z hz) (attB z hz) p (Sum.inl (Sum.inl y)) = true} ≤ 3 := by
  rw [card_sum_split]
  have h1 : Fintype.card {a : U (z+1) z t //
      rel' z t J (attA z hz) (attB z hz) (Sum.inl a) (Sum.inl (Sum.inl y)) = true} =
      Fintype.card {a : U (z+1) z t // adj (z+1) z t a (Sum.inl y) = true} := rfl
  rw [h1]
  have hge := (baseR_ge2 z hz _).trans (old_right_ge z t ht y)
  have hear : Fintype.card {h : EP J //
      rel' z t J (attA z hz) (attB z hz) (Sum.inr h) (Sum.inl (Sum.inl y)) = true} ≤ 1 := by
    apply card_le_one_of
    intro h h' hh hh'
    simp only [rel', Sum.elim_inl, Sum.elim_inr, decide_eq_true_eq, Sum.inl.injEq] at hh hh'
    have hc : h.1 = h'.1 := attB_inj z hz (hh.1.symm.trans hh'.1)
    refine ep_ext hc ?_
    have e1 := hh.2
    have e2 := hh'.2
    have e3 : J h.1 = J h'.1 := congrArg J hc
    omega
  by_cases hB : ∃ c, y = attB z hz c
  · obtain ⟨c, rfl⟩ := hB
    obtain ⟨s, hs⟩ := attB_symm z hz c
    have hle := old_right_le z t ht (attB z hz c)
    rw [hs] at hle
    have hb := baseR_conn_le2 z s
    omega
  · have h0 : Fintype.card {h : EP J //
        rel' z t J (attA z hz) (attB z hz) (Sum.inr h) (Sum.inl (Sum.inl y)) = true} = 0 := by
      apply card_zero_of
      intro h hh
      simp only [rel', Sum.elim_inl, Sum.elim_inr, decide_eq_true_eq, Sum.inl.injEq] at hh
      exact hB ⟨h.1, hh.1⟩
    have := adj_deg_R_le3 z t hz y
    omega

end Degrees

theorem raw_left (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) (ht : 1 ≤ t) (p : U' z t J) :
    2 ≤ Fintype.card {q // rel' z t J (attA z hz) (attB z hz) p q = true} ∧
    Fintype.card {q // rel' z t J (attA z hz) (attB z hz) p q = true} ≤ 3 := by
  rcases p with (x | ⟨e, j⟩) | q
  · exact old_left_deg z t J hz ht x
  · rw [← tpg_fin z t J e j]
    obtain ⟨n1, n2, n3⟩ := t_np_in z t J hz e j.val j.isLt
    exact two_of_path _ _ _ (t_np z t J hz e j.val j.isLt) n1 n2 n3
  · rw [← epg_fin z t J hz q]
    obtain ⟨n1, n2, n3⟩ := e_np_in z t J hz q.1 q.2.val q.2.isLt
    exact two_of_path _ _ _ (e_np z t J hz q.1 q.2.val q.2.isLt) n1 n2 n3

theorem raw_right (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) (ht : 1 ≤ t) (q : V' z t J) :
    2 ≤ Fintype.card {p // rel' z t J (attA z hz) (attB z hz) p q = true} ∧
    Fintype.card {p // rel' z t J (attA z hz) (attB z hz) p q = true} ≤ 3 := by
  rcases q with (y | ⟨e, j⟩) | q
  · exact old_right_deg z t J hz ht y
  · rw [← thl_fin z t J e j]
    obtain ⟨n1, n2, n3⟩ := t_nh_in z t J hz e j.val j.isLt
    exact two_of_path _ _ _ (t_nh z t J hz e j.val j.isLt) n1 n2 n3
  · rw [← ehl_fin z t J hz q]
    obtain ⟨n1, n2, n3⟩ := e_nh_in z t J hz q.1 q.2.val q.2.isLt
    exact two_of_path _ _ _ (e_nh z t J hz q.1 q.2.val q.2.isLt) n1 n2 n3

section Conn

theorem base_conn (z : ℕ) (hz : 2 ≤ z) (gL : L (z+1) z → Bool) (gR : R (z+1) z → Bool)
    (hg : ∀ x y, baseAdj (z+1) z x y = true → gL x = gR y) :
    (∀ x, gL x = gL (Sum.inl (⟨0, by omega⟩, ⟨0, by omega⟩))) ∧
    (∀ y, gR y = gL (Sum.inl (⟨0, by omega⟩, ⟨0, by omega⟩))) := by
  have row : ∀ (i : Fin (z+1)) (j : ℕ) (hj : j < z),
      gL (Sum.inl (i, ⟨j, hj⟩)) = gL (Sum.inl (i, ⟨0, by omega⟩)) := by
    intro i j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      rw [← ih (by omega)]
      rw [hg (Sum.inl (i, ⟨j + 1, hj⟩)) (Sum.inr (i, ⟨j, by omega⟩)) (by simp [baseAdj]),
        hg (Sum.inl (i, ⟨j, by omega⟩)) (Sum.inr (i, ⟨j, by omega⟩)) (by simp [baseAdj])]
  have col : ∀ (i : ℕ) (hi : i < z + 1),
      gR (Sum.inl (⟨i, hi⟩, ⟨0, by omega⟩)) = gR (Sum.inl (⟨0, by omega⟩, ⟨0, by omega⟩)) := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      rw [← ih (by omega)]
      rw [← hg (Sum.inr (⟨i, by omega⟩, ⟨0, by omega⟩)) (Sum.inl (⟨i + 1, hi⟩, ⟨0, by omega⟩))
          (by simp [baseAdj]),
        ← hg (Sum.inr (⟨i, by omega⟩, ⟨0, by omega⟩)) (Sum.inl (⟨i, by omega⟩, ⟨0, by omega⟩))
          (by simp [baseAdj])]
  have cell : ∀ (i : Fin (z+1)) (j : Fin z),
      gL (Sum.inl (i, j)) = gL (Sum.inl (⟨0, by omega⟩, ⟨0, by omega⟩)) := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    rw [row ⟨i, hi⟩ j hj, hg (Sum.inl (⟨i, hi⟩, ⟨0, by omega⟩)) (Sum.inl (⟨i, hi⟩, ⟨0, by omega⟩))
      (by simp [baseAdj]), col i hi, ← hg (Sum.inl (⟨0, by omega⟩, ⟨0, by omega⟩))
      (Sum.inl (⟨0, by omega⟩, ⟨0, by omega⟩)) (by simp [baseAdj])]
  have cellR : ∀ (i : Fin (z+1)) (j : Fin z),
      gR (Sum.inl (i, j)) = gL (Sum.inl (⟨0, by omega⟩, ⟨0, by omega⟩)) := by
    intro i j
    rw [← hg (Sum.inl (i, j)) (Sum.inl (i, j)) (by simp [baseAdj])]
    exact cell i j
  refine ⟨?_, ?_⟩
  · rintro (⟨i, j⟩ | ⟨i, j⟩)
    · exact cell i j
    · have hi := i.isLt
      rw [hg (Sum.inr (i, j)) (Sum.inl (⟨i.val, by omega⟩, j)) (by simp [baseAdj])]
      exact cellR _ _
  · rintro (⟨i, j⟩ | ⟨i, j⟩)
    · exact cellR i j
    · have hj := j.isLt
      rw [← hg (Sum.inl (i, ⟨j.val, by omega⟩)) (Sum.inr (i, j)) (by simp [baseAdj])]
      exact cell _ _

theorem raw_conn (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) (ht : 1 ≤ t) :
    ∀ col : U' z t J ⊕ V' z t J → Bool, (∀ p q, rel' z t J (attA z hz) (attB z hz) p q = true →
      col (Sum.inl p) = col (Sum.inr q)) → ∀ x y, col x = col y := by
  intro col hc
  let fL : Fin (Fintype.card (L (z+1) z)) → Bool := fun x => col (Sum.inl (Sum.inl (Sum.inl x)))
  let fR : Fin (Fintype.card (R (z+1) z)) → Bool := fun y => col (Sum.inr (Sum.inl (Sum.inl y)))
  have thr : ∀ e : E (z+1) z, ∀ j, j < t → col (Sum.inl (tpg z t J e j)) = fL e.val.1 := by
    intro e j
    induction j with
    | zero =>
      intro hj
      obtain ⟨n1, -, -⟩ := t_np_in z t J hz e 0 hj
      obtain ⟨-, m2, -⟩ := t_nh_in z t J hz e 0 hj
      rw [if_pos rfl] at m2
      rw [hc _ _ n1, ← hc _ _ m2]
    | succ j ih =>
      intro hj
      obtain ⟨n1, -, -⟩ := t_np_in z t J hz e (j + 1) hj
      obtain ⟨-, m2, -⟩ := t_nh_in z t J hz e (j + 1) hj
      rw [if_neg (by omega), Nat.add_sub_cancel] at m2
      rw [hc _ _ n1, ← hc _ _ m2, ih (by omega)]
  have thrR : ∀ e : E (z+1) z, ∀ j, j < t → col (Sum.inr (thl z t J e j)) = fL e.val.1 := by
    intro e j hj
    obtain ⟨n1, -, -⟩ := t_np_in z t J hz e j hj
    rw [← hc _ _ n1, thr e j hj]
  have endR : ∀ e : E (z+1) z, fR e.val.2 = fL e.val.1 := by
    intro e
    obtain ⟨-, n2, -⟩ := t_np_in z t J hz e (t - 1) (by omega)
    rw [if_neg (by omega)] at n2
    change col (Sum.inr (Sum.inl (Sum.inl e.val.2))) = fL e.val.1
    rw [← hc _ _ n2, thr e (t - 1) (by omega)]
  have ear : ∀ c : Bool, ∀ j, j < J c → col (Sum.inl (epg z t J hz c j)) = fL (attA z hz c) := by
    intro c j
    induction j with
    | zero =>
      intro hj
      obtain ⟨n1, -, -⟩ := e_np_in z t J hz c 0 hj
      obtain ⟨-, m2, -⟩ := e_nh_in z t J hz c 0 hj
      rw [if_pos rfl] at m2
      rw [hc _ _ n1, ← hc _ _ m2]
    | succ j ih =>
      intro hj
      obtain ⟨n1, -, -⟩ := e_np_in z t J hz c (j + 1) hj
      obtain ⟨-, m2, -⟩ := e_nh_in z t J hz c (j + 1) hj
      rw [if_neg (by omega), Nat.add_sub_cancel] at m2
      rw [hc _ _ n1, ← hc _ _ m2, ih (by omega)]
  have earR : ∀ c : Bool, ∀ j, j < J c → col (Sum.inr (ehl z t J hz c j)) = fL (attA z hz c) := by
    intro c j hj
    obtain ⟨n1, -, -⟩ := e_np_in z t J hz c j hj
    rw [← hc _ _ n1, ear c j hj]
  obtain ⟨bL, bR⟩ := base_conn z hz (fun x => fL (Fintype.equivFin _ x))
    (fun y => fR (Fintype.equivFin _ y)) (by
      intro x y hxy
      have := endR ⟨(Fintype.equivFin _ x, Fintype.equivFin _ y),
        (H_mem z _ _).mpr (by simpa only [Equiv.symm_apply_apply] using hxy)⟩
      exact this.symm)
  have oL : ∀ x, fL x = fL (Fintype.equivFin _ (Sum.inl (⟨0, by omega⟩, ⟨0, by omega⟩))) := by
    intro x
    have := bL ((Fintype.equivFin _).symm x)
    simpa only [Equiv.apply_symm_apply] using this
  have oR : ∀ y, fR y = fL (Fintype.equivFin _ (Sum.inl (⟨0, by omega⟩, ⟨0, by omega⟩))) := by
    intro y
    have := bR ((Fintype.equivFin _).symm y)
    simpa only [Equiv.apply_symm_apply] using this
  suffices key : ∀ w, col w = fL (Fintype.equivFin _ (Sum.inl (⟨0, by omega⟩, ⟨0, by omega⟩))) by
    intro x y
    rw [key x, key y]
  rintro (((x | ⟨e, j⟩) | q) | ((y | ⟨e, j⟩) | q))
  · exact oL x
  · rw [← tpg_fin z t J e j, thr e j.val j.isLt, oL e.val.1]
  · rw [← epg_fin z t J hz q, ear q.1 q.2.val q.2.isLt, oL (attA z hz q.1)]
  · exact oR y
  · rw [← thl_fin z t J e j, thrR e j.val j.isLt, oL e.val.1]
  · rw [← ehl_fin z t J hz q, earR q.1 q.2.val q.2.isLt, oL (attA z hz q.1)]

end Conn

section Girth

theorem cyc_nbrs_left {P Q : Type} (R : P → Q → Bool) {s : ℕ} (us : Fin (s+2) ↪ P)
    (vs : Fin (s+2) ↪ Q) (h : ∀ i, R (us i) (vs i) = true ∧ R (us (i+1)) (vs i) = true)
    (i : Fin (s+2)) (y1 y2 : Q) (hn : ∀ y, R (us i) y = true → y = y1 ∨ y = y2) :
    (∃ j, vs j = y1) ∧ (∃ j, vs j = y2) := by
  have ha := (h i).1
  have hb : R (us i) (vs (i - 1)) = true := by
    have := (h (i - 1)).2
    rwa [sub_add_cancel] at this
  have hne : vs i ≠ vs (i - 1) := by
    intro he
    have h1 := vs.injective he
    have h2 : (1 : Fin (s+2)) = 0 := sub_eq_self.mp h1.symm
    have h3 := congrArg Fin.val h2
    simp only [Fin.val_one, Fin.val_zero] at h3
    omega
  rcases hn _ ha with h1 | h1 <;> rcases hn _ hb with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · exact ⟨⟨i, h1⟩, ⟨i - 1, h2⟩⟩
  · exact ⟨⟨i - 1, h2⟩, ⟨i, h1⟩⟩
  · exact absurd (h1.trans h2.symm) hne

theorem cyc_nbrs_right {P Q : Type} (R : P → Q → Bool) {s : ℕ} (us : Fin (s+2) ↪ P)
    (vs : Fin (s+2) ↪ Q) (h : ∀ i, R (us i) (vs i) = true ∧ R (us (i+1)) (vs i) = true)
    (i : Fin (s+2)) (x1 x2 : P) (hn : ∀ x, R x (vs i) = true → x = x1 ∨ x = x2) :
    (∃ j, us j = x1) ∧ (∃ j, us j = x2) := by
  have ha := (h i).1
  have hb := (h i).2
  have hne : us i ≠ us (i + 1) := by
    intro he
    have h1 := us.injective he
    have h2 : (1 : Fin (s+2)) = 0 := by
      have := congrArg (fun x => x - i) h1
      simpa using this.symm
    have h3 := congrArg Fin.val h2
    simp only [Fin.val_one, Fin.val_zero] at h3
    omega
  rcases hn _ ha with h1 | h1 <;> rcases hn _ hb with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · exact ⟨⟨i, h1⟩, ⟨i + 1, h2⟩⟩
  · exact ⟨⟨i + 1, h2⟩, ⟨i, h1⟩⟩
  · exact absurd (h1.trans h2.symm) hne

theorem path_cover {P Q : Type} (R : P → Q → Bool) {s : ℕ} (us : Fin (s+2) ↪ P)
    (vs : Fin (s+2) ↪ Q) (h : ∀ i, R (us i) (vs i) = true ∧ R (us (i+1)) (vs i) = true)
    (n : ℕ) (pg : ℕ → P) (hl : ℕ → Q) (endP : P) (endH : Q)
    (hinj : ∀ j j', j < n → j' < n → pg j = pg j' → j = j')
    (NP : ∀ j < n, ∀ y, R (pg j) y = true →
      y = hl j ∨ y = (if j + 1 < n then hl (j + 1) else endH))
    (NH : ∀ j < n, ∀ x, R x (hl j) = true → x = pg j ∨ x = (if j = 0 then endP else pg (j - 1)))
    (j0 : ℕ) (hj0 : j0 < n) (h0 : (∃ i, us i = pg j0) ∨ (∃ i, vs i = hl j0)) : n ≤ s + 2 := by
  have up : ∀ j, j + 1 < n → (∃ i, us i = pg j) → (∃ i, us i = pg (j + 1)) := by
    rintro j hj ⟨i, hi⟩
    obtain ⟨-, ⟨i2, hi2⟩⟩ := cyc_nbrs_left R us vs h i (hl j)
      (if j + 1 < n then hl (j + 1) else endH) (by rw [hi]; exact NP j (by omega))
    rw [if_pos hj] at hi2
    obtain ⟨⟨i3, hi3⟩, -⟩ := cyc_nbrs_right R us vs h i2 (pg (j + 1))
      (if j + 1 = 0 then endP else pg (j + 1 - 1)) (by rw [hi2]; exact NH (j + 1) hj)
    exact ⟨i3, hi3⟩
  have down : ∀ j, j < n → 1 ≤ j → (∃ i, us i = pg j) → (∃ i, us i = pg (j - 1)) := by
    rintro j hj hj1 ⟨i, hi⟩
    obtain ⟨⟨i2, hi2⟩, -⟩ := cyc_nbrs_left R us vs h i (hl j)
      (if j + 1 < n then hl (j + 1) else endH) (by rw [hi]; exact NP j hj)
    obtain ⟨-, ⟨i3, hi3⟩⟩ := cyc_nbrs_right R us vs h i2 (pg j)
      (if j = 0 then endP else pg (j - 1)) (by rw [hi2]; exact NH j hj)
    rw [if_neg (by omega)] at hi3
    exact ⟨i3, hi3⟩
  have start : ∃ i, us i = pg j0 := by
    rcases h0 with h0 | ⟨i, hi⟩
    · exact h0
    · obtain ⟨⟨i3, hi3⟩, -⟩ := cyc_nbrs_right R us vs h i (pg j0)
        (if j0 = 0 then endP else pg (j0 - 1)) (by rw [hi]; exact NH j0 hj0)
      exact ⟨i3, hi3⟩
  have hup : ∀ d, j0 + d < n → ∃ i, us i = pg (j0 + d) := by
    intro d
    induction d with
    | zero => intro _; exact start
    | succ d ih => intro hd; exact up (j0 + d) (by omega) (ih (by omega))
  have hdown : ∀ d, d ≤ j0 → ∃ i, us i = pg (j0 - d) := by
    intro d
    induction d with
    | zero => intro _; simpa using start
    | succ d ih =>
      intro hd
      have := down (j0 - d) (by omega) (by omega) (ih (by omega))
      rwa [show j0 - d - 1 = j0 - (d + 1) by omega] at this
  have all : ∀ j, j < n → ∃ i, us i = pg j := by
    intro j hj
    by_cases hjj : j0 ≤ j
    · have := hup (j - j0) (by omega)
      rwa [show j0 + (j - j0) = j by omega] at this
    · have := hdown (j0 - j) (by omega)
      rwa [show j0 - (j0 - j) = j by omega] at this
  choose f hf using fun j : Fin n => all j.val j.isLt
  have finj : Function.Injective f := by
    intro a b hab
    apply Fin.ext
    apply hinj a b a.isLt b.isLt
    rw [← hf a, ← hf b, hab]
  simpa using Fintype.card_le_of_injective f finj

theorem raw_girth (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) (ht : 1 ≤ t)
    (hJ : ∀ c, J c = 0 ∨ t ≤ J c) (s : ℕ) (us : Fin (s+2) ↪ U' z t J) (vs : Fin (s+2) ↪ V' z t J)
    (h : ∀ i, rel' z t J (attA z hz) (attB z hz) (us i) (vs i) = true ∧
      rel' z t J (attA z hz) (attB z hz) (us (i+1)) (vs i) = true) : t ≤ s + 2 := by
  have thread : ∀ (e : E (z+1) z) (j : Fin t),
      ((∃ i, us i = tpg z t J e j.val) ∨ (∃ i, vs i = thl z t J e j.val)) → t ≤ s + 2 := by
    intro e j h0
    refine path_cover _ us vs h t (tpg z t J e) (thl z t J e) _ _ ?_ (t_np z t J hz e)
      (t_nh z t J hz e) j.val j.isLt h0
    intro a b ha hb hab
    simp only [tpg, dif_pos ha, dif_pos hb, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq,
      Fin.mk.injEq, true_and] at hab
    exact hab
  have ear : ∀ (c : Bool) (j : Fin (J c)),
      ((∃ i, us i = epg z t J hz c j.val) ∨ (∃ i, vs i = ehl z t J hz c j.val)) → t ≤ s + 2 := by
    intro c j h0
    have hn := path_cover _ us vs h (J c) (epg z t J hz c) (ehl z t J hz c) _ _ ?_
      (e_np z t J hz c) (e_nh z t J hz c) j.val j.isLt h0
    · rcases hJ c with h1 | h1
      · have := j.isLt; omega
      · omega
    · intro a b ha hb hab
      simp only [epg, dif_pos ha, dif_pos hb] at hab
      have := congrArg (fun x : U' z t J => Sum.elim (fun _ => 0) (fun q : EP J => q.2.val) x) hab
      simpa using this
  have h0 := (h 0).1
  rcases hu : us 0 with (x | ⟨e, j⟩) | q
  · rw [hu] at h0
    rcases hv : vs 0 with (v | ⟨e, j⟩) | q
    · rw [hv] at h0
      simp only [rel', Sum.elim_inl, adj, decide_eq_true_eq] at h0
      exact absurd h0.1 (by omega)
    · exact thread e j (Or.inr ⟨0, by rw [hv, thl_fin]⟩)
    · exact ear q.1 q.2 (Or.inr ⟨0, by rw [hv, ehl_fin]⟩)
  · exact thread e j (Or.inl ⟨0, by rw [hu, tpg_fin]⟩)
  · exact ear q.1 q.2 (Or.inl ⟨0, by rw [hu, epg_fin]⟩)

end Girth

noncomputable def oldE (z t : ℕ) (J : Bool → ℕ) :
    U' z t J → V' z t J → Option (GEdge (G (z+1) z t))
  | Sum.inl p, Sum.inl q => if h : adj (z+1) z t p q = true then
      some ⟨(Fintype.equivFin _ p, Fintype.equivFin _ q), by
        simp only [G, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
        exact h⟩ else none
  | _, _ => none

def ntE (z t : ℕ) (J : Bool → ℕ) : U' z t J → V' z t J → Bool
  | Sum.inr x, Sum.inr y => decide (x.2.val = y.2.val)
  | _, _ => false

theorem old_nt (z t : ℕ) (J : Bool → ℕ) (x : U' z t J) (y : V' z t J) (w : GEdge (G (z+1) z t))
    (h : oldE z t J x y = some w) : ntE z t J x y = false := by
  rcases x with x | x <;> rcases y with y | y <;> simp_all [oldE, ntE]

theorem old_spec (z t : ℕ) (J : Bool → ℕ) (x : U' z t J) (y : V' z t J) (w : GEdge (G (z+1) z t))
    (h : oldE z t J x y = some w) :
    ∃ p q, x = Sum.inl p ∧ y = Sum.inl q ∧ w.1 = (Fintype.equivFin _ p, Fintype.equivFin _ q) := by
  rcases x with p | x <;> rcases y with q | y <;> simp only [oldE, reduceCtorEq] at h
  split at h
  · simp only [Option.some.injEq] at h
    exact ⟨p, q, rfl, rfl, by rw [← h]⟩
  · simp at h

theorem old_none_r (z t : ℕ) (J : Bool → ℕ) (x : U' z t J) (y : EP J) :
    oldE z t J x (Sum.inr y) = none := by
  rcases x with x | x <;> rfl

theorem old_none_l (z t : ℕ) (J : Bool → ℕ) (x : EP J) (y : V' z t J) :
    oldE z t J (Sum.inr x) y = none := by
  rcases y with y | y <;> rfl

theorem nt_spec (z t : ℕ) (J : Bool → ℕ) (A : Bool → Fin (Fintype.card (L (z+1) z)))
    (B : Bool → Fin (Fintype.card (R (z+1) z))) (x : U' z t J) (y : V' z t J)
    (h1 : ntE z t J x y = true) (h2 : rel' z t J A B x y = true) :
    ∃ c, x = Sum.inr c ∧ y = Sum.inr c := by
  rcases x with x | x <;> rcases y with y | y <;> simp only [ntE, reduceCtorEq] at h1
  · simp only [rel', Sum.elim_inr, decide_eq_true_eq] at h1 h2
    exact ⟨x, rfl, by rw [ep_ext h2.1.symm h1.symm]⟩

theorem value_iff {W : Type} (a : W → Bool) (o : Option W) (b : Bool) (h : o = none ∨ b = false) :
    (Bool.xor (decide (Odd ((o.toFinset).filter (fun v => a v = true)).card)) b) = true ↔
      ((∃ w, o = some w ∧ a w = true) ∨ b = true) := by
  rcases o with _ | w
  · simp
  · rcases h with h | h
    · simp at h
    · subst h
      by_cases hw : a w = true <;> simp [hw, Finset.filter_singleton]

noncomputable abbrev Gr' (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) :=
  graph z t J (attA z hz) (attB z hz) hz

noncomputable def supE (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) :
    GEdge (Gr' z t J hz) → Finset (GEdge (G (z+1) z t)) := fun e =>
  (oldE z t J (eU z t J hz e.1.1) (eV z t J e.1.2)).toFinset

noncomputable def cstE (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) : GEdge (Gr' z t J hz) → Bool :=
  fun e => ntE z t J (eU z t J hz e.1.1) (eV z t J e.1.2)

theorem hmem' (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) (u : Fin (Fintype.card (V' z t J) + 1))
    (v : Fin (Fintype.card (V' z t J))) :
    v ∈ Gr' z t J hz u ↔ rel' z t J (attA z hz) (attB z hz) (eU z t J hz u) (eV z t J v) = true :=
  mem_relG _ _ _ u v

theorem hv' (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) (a : GEdge (G (z+1) z t) → Bool)
    (e : GEdge (Gr' z t J hz)) :
    PEqualNP.Outside.L_pcx_341_aux.Replay.value (supE z t J hz) (cstE z t J hz) a e = true ↔
      ((∃ w, oldE z t J (eU z t J hz e.1.1) (eV z t J e.1.2) = some w ∧ a w = true) ∨
        ntE z t J (eU z t J hz e.1.1) (eV z t J e.1.2) = true) := by
  have hpre : oldE z t J (eU z t J hz e.1.1) (eV z t J e.1.2) = none ∨
      ntE z t J (eU z t J hz e.1.1) (eV z t J e.1.2) = false := by
    rcases Option.eq_none_or_eq_some (oldE z t J (eU z t J hz e.1.1) (eV z t J e.1.2)) with h | ⟨w, h⟩
    · exact Or.inl h
    · exact Or.inr (old_nt z t J _ _ w h)
  exact value_iff a _ _ hpre

theorem hold' (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) : ∀ a e w,
    oldE z t J (eU z t J hz e.1.1) (eV z t J e.1.2) = some w →
      (PEqualNP.Outside.L_pcx_341_aux.Replay.value (supE z t J hz) (cstE z t J hz) a e = true ↔ a w = true) := by
  intro a e w hw
  rw [hv' z t J hz, hw, old_nt z t J _ _ w hw]
  simp

theorem hNT' (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) : ∀ a e, PEqualNP.Outside.L_pcx_341_aux.Replay.value (supE z t J hz) (cstE z t J hz) a e = true →
      oldE z t J (eU z t J hz e.1.1) (eV z t J e.1.2) = none →
      ∃ c, eU z t J hz e.1.1 = Sum.inr c ∧ eV z t J e.1.2 = Sum.inr c := by
  intro a e h1 h2
  rcases (hv' z t J hz a e).mp h1 with ⟨w, hw, -⟩ | h3
  · rw [h2] at hw; exact absurd hw (by simp)
  · exact nt_spec z t J _ _ _ _ h3 ((hmem' z t J hz _ _).mp e.2)

theorem D0' (z t : ℕ) (hz : 2 ≤ z) : ∃ D, D ∈ funGraphPHP (G (z+1) z t) :=
  ⟨_, Or.inl (Or.inl ⟨Fintype.equivFin _ (Sum.inl (Fintype.equivFin _
    (Sum.inl ((⟨0, by omega⟩ : Fin (z+1)), (⟨0, by omega⟩ : Fin z))))), rfl⟩)⟩

theorem pig_sat {m n : ℕ} (G' : BipGraph m n) (a : GEdge G' → Bool) (i : Fin m) :
    ClauseSat a (Finset.univ.filter (fun l : Literal (GEdge G') => l.1.1.1 = i ∧ l.2 = true)) ↔
      ∃ e : GEdge G', e.1.1 = i ∧ a e = true := by
  constructor
  · rintro ⟨l, hl, hal⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    exact ⟨l.1, hl.1, hal.trans hl.2⟩
  · rintro ⟨e, he, hae⟩
    exact ⟨(e, true), by simp [he], hae⟩

theorem G_mem (z t : ℕ) (u : Fin (Fintype.card (U (z+1) z t)))
    (v : Fin (Fintype.card (V (z+1) z t))) : v ∈ G (z+1) z t u ↔
      adj (z+1) z t ((Fintype.equivFin _).symm u) ((Fintype.equivFin _).symm v) = true := by
  simp only [G, Finset.mem_filter, Finset.mem_univ, true_and]

set_option maxHeartbeats 1000000 in
theorem hax_pig_old (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) (i : Fin (Fintype.card (V' z t J) + 1))
    (p : U (z+1) z t) (hx : eU z t J hz i = Sum.inl p) :
    ∃ D ∈ funGraphPHP (G (z+1) z t), ∀ a, ClauseSat a D → ClauseSat (PEqualNP.Outside.L_pcx_341_aux.Replay.value (supE z t J hz) (cstE z t J hz) a)
      (Finset.univ.filter (fun l : Literal (GEdge (Gr' z t J hz)) => l.1.1.1 = i ∧ l.2 = true)) := by
  refine ⟨Finset.univ.filter (fun l : Literal (GEdge (G (z+1) z t)) =>
    l.1.1.1 = Fintype.equivFin _ p ∧ l.2 = true), Or.inl (Or.inl ⟨_, rfl⟩), fun a ha => ?_⟩
  obtain ⟨w, hw1, hal⟩ := (pig_sat _ a _).mp ha
  have hadj : adj (z+1) z t p ((Fintype.equivFin _).symm w.1.2) = true := by
    rw [← Equiv.symm_apply_apply (Fintype.equivFin (U (z+1) z t)) p, ← hw1]
    exact (G_mem z t _ _).mp w.2
  refine (pig_sat _ _ _).mpr ⟨⟨(i, (eV z t J).symm (Sum.inl ((Fintype.equivFin _).symm w.1.2))),
    (hmem' z t J hz _ _).mpr (by rw [hx, Equiv.apply_symm_apply]; exact hadj)⟩, rfl, ?_⟩
  apply (hold' z t J hz a _ w ?_).mpr hal
  simp only [hx, Equiv.apply_symm_apply, oldE, hadj, dite_true, Option.some.injEq]
  apply Subtype.ext
  simp only [Equiv.apply_symm_apply]
  exact Prod.ext hw1.symm rfl

set_option maxHeartbeats 1000000 in
theorem hax_pig_ear (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) (i : Fin (Fintype.card (V' z t J) + 1))
    (x : EP J) (hx : eU z t J hz i = Sum.inr x) :
    ∃ D ∈ funGraphPHP (G (z+1) z t), ∀ a, ClauseSat a D → ClauseSat (PEqualNP.Outside.L_pcx_341_aux.Replay.value (supE z t J hz) (cstE z t J hz) a)
      (Finset.univ.filter (fun l : Literal (GEdge (Gr' z t J hz)) => l.1.1.1 = i ∧ l.2 = true)) := by
  obtain ⟨D0, hD0⟩ := D0' z t hz
  refine ⟨D0, hD0, fun a _ => (pig_sat _ _ _).mpr ⟨⟨(i, (eV z t J).symm (Sum.inr x)),
    (hmem' z t J hz _ _).mpr (by rw [hx, Equiv.apply_symm_apply]; simp [rel'])⟩, rfl, ?_⟩⟩
  apply (hv' z t J hz a _).mpr (Or.inr ?_)
  simp [hx, ntE]

theorem hax_pig (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) (i : Fin (Fintype.card (V' z t J) + 1)) :
    ∃ D ∈ funGraphPHP (G (z+1) z t), ∀ a, ClauseSat a D → ClauseSat (PEqualNP.Outside.L_pcx_341_aux.Replay.value (supE z t J hz) (cstE z t J hz) a)
      (Finset.univ.filter (fun l : Literal (GEdge (Gr' z t J hz)) => l.1.1.1 = i ∧ l.2 = true)) := by
  rcases hx : eU z t J hz i with p | x
  · exact hax_pig_old z t J hz i p hx
  · exact hax_pig_ear z t J hz i x hx

set_option maxHeartbeats 1000000 in
theorem hax_hole (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) (e e' : GEdge (Gr' z t J hz))
    (hsame : e.1.2 = e'.1.2) (hne : e.1.1 ≠ e'.1.1) :
    ∃ D ∈ funGraphPHP (G (z+1) z t), ∀ a, ClauseSat a D → ClauseSat (PEqualNP.Outside.L_pcx_341_aux.Replay.value (supE z t J hz) (cstE z t J hz) a)
      {(e, false), (e', false)} := by
  classical
  have hmem := hmem' z t J hz
  have hv := hv' z t J hz
  have hold := hold' z t J hz
  have hNT := hNT' z t J hz
  obtain ⟨D0, hD0⟩ := D0' z t hz
  by_cases ho : ∃ w w', oldE z t J (eU z t J hz e.1.1) (eV z t J e.1.2) = some w ∧
      oldE z t J (eU z t J hz e'.1.1) (eV z t J e'.1.2) = some w'
  · obtain ⟨w, w', hw, hw'⟩ := ho
    obtain ⟨p, q, hp, hq, hwe⟩ := old_spec z t J _ _ w hw
    obtain ⟨p', q', hp', hq', hwe'⟩ := old_spec z t J _ _ w' hw'
    refine ⟨{(w, false), (w', false)}, Or.inl (Or.inr ⟨w, w', ?_, ?_, rfl⟩), ?_⟩
    · rw [hwe, hwe']
      have : Sum.inl q = (Sum.inl q' : V' z t J) := by rw [← hq, ← hq', hsame]
      simp only [Sum.inl.injEq] at this
      simp [this]
    · rw [hwe, hwe']
      intro hpp
      apply hne
      have : p = p' := (Fintype.equivFin _).injective hpp
      apply (eU z t J hz).injective
      rw [hp, hp', this]
    · rintro a ⟨l, hl, hal⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl
      · refine ⟨(e, false), by simp, ?_⟩
        have := hold a e w hw
        simp only at hal ⊢
        cases hve : PEqualNP.Outside.L_pcx_341_aux.Replay.value (supE z t J hz) (cstE z t J hz) a e
        · rfl
        · rw [this.mp hve] at hal; exact absurd hal (by simp)
      · refine ⟨(e', false), by simp, ?_⟩
        have := hold a e' w' hw'
        simp only at hal ⊢
        cases hve : PEqualNP.Outside.L_pcx_341_aux.Replay.value (supE z t J hz) (cstE z t J hz) a e'
        · rfl
        · rw [this.mp hve] at hal; exact absurd hal (by simp)
  · refine ⟨D0, hD0, fun a _ => ?_⟩
    by_contra hcon
    have h1 : PEqualNP.Outside.L_pcx_341_aux.Replay.value (supE z t J hz) (cstE z t J hz) a e = true := by
      by_contra h; apply hcon; exact ⟨(e, false), by simp, by simpa using h⟩
    have h2 : PEqualNP.Outside.L_pcx_341_aux.Replay.value (supE z t J hz) (cstE z t J hz) a e' = true := by
      by_contra h; apply hcon; exact ⟨(e', false), by simp, by simpa using h⟩
    have key : ∀ (f f' : GEdge (Gr' z t J hz)), f.1.2 = f'.1.2 →
        PEqualNP.Outside.L_pcx_341_aux.Replay.value (supE z t J hz) (cstE z t J hz) a f = true →
        PEqualNP.Outside.L_pcx_341_aux.Replay.value (supE z t J hz) (cstE z t J hz) a f' = true →
        oldE z t J (eU z t J hz f.1.1) (eV z t J f.1.2) = none → f.1.1 = f'.1.1 := by
      intro f f' hff hf hf' hn
      obtain ⟨c, hc1, hc2⟩ := hNT a f hf hn
      have hn' : oldE z t J (eU z t J hz f'.1.1) (eV z t J f'.1.2) = none := by
        rw [← hff, hc2, old_none_r]
      obtain ⟨c', hc1', hc2'⟩ := hNT a f' hf' hn'
      rw [← hff, hc2] at hc2'
      simp only [Sum.inr.injEq] at hc2'
      apply (eU z t J hz).injective
      rw [hc1, hc1', hc2']
    by_cases hn : oldE z t J (eU z t J hz e.1.1) (eV z t J e.1.2) = none
    · exact hne (key e e' hsame h1 h2 hn)
    · by_cases hn' : oldE z t J (eU z t J hz e'.1.1) (eV z t J e'.1.2) = none
      · exact hne (key e' e hsame.symm h2 h1 hn').symm
      · apply ho
        obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hn
        obtain ⟨w', hw'⟩ := Option.ne_none_iff_exists'.mp hn'
        exact ⟨w, w', hw, hw'⟩

set_option maxHeartbeats 1000000 in
theorem hax_fun (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) (e e' : GEdge (Gr' z t J hz))
    (hsame : e.1.1 = e'.1.1) (hne : e.1.2 ≠ e'.1.2) :
    ∃ D ∈ funGraphPHP (G (z+1) z t), ∀ a, ClauseSat a D → ClauseSat (PEqualNP.Outside.L_pcx_341_aux.Replay.value (supE z t J hz) (cstE z t J hz) a)
      {(e, false), (e', false)} := by
  classical
  have hmem := hmem' z t J hz
  have hv := hv' z t J hz
  have hold := hold' z t J hz
  have hNT := hNT' z t J hz
  obtain ⟨D0, hD0⟩ := D0' z t hz
  by_cases ho : ∃ w w', oldE z t J (eU z t J hz e.1.1) (eV z t J e.1.2) = some w ∧
      oldE z t J (eU z t J hz e'.1.1) (eV z t J e'.1.2) = some w'
  · obtain ⟨w, w', hw, hw'⟩ := ho
    obtain ⟨p, q, hp, hq, hwe⟩ := old_spec z t J _ _ w hw
    obtain ⟨p', q', hp', hq', hwe'⟩ := old_spec z t J _ _ w' hw'
    refine ⟨{(w, false), (w', false)}, Or.inr ⟨w, w', ?_, ?_, rfl⟩, ?_⟩
    · rw [hwe, hwe']
      have : Sum.inl p = (Sum.inl p' : U' z t J) := by rw [← hp, ← hp', hsame]
      simp only [Sum.inl.injEq] at this
      simp [this]
    · rw [hwe, hwe']
      intro hqq
      apply hne
      have : q = q' := (Fintype.equivFin _).injective hqq
      apply (eV z t J).injective
      rw [hq, hq', this]
    · rintro a ⟨l, hl, hal⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl
      · refine ⟨(e, false), by simp, ?_⟩
        have := hold a e w hw
        simp only at hal ⊢
        cases hve : PEqualNP.Outside.L_pcx_341_aux.Replay.value (supE z t J hz) (cstE z t J hz) a e
        · rfl
        · rw [this.mp hve] at hal; exact absurd hal (by simp)
      · refine ⟨(e', false), by simp, ?_⟩
        have := hold a e' w' hw'
        simp only at hal ⊢
        cases hve : PEqualNP.Outside.L_pcx_341_aux.Replay.value (supE z t J hz) (cstE z t J hz) a e'
        · rfl
        · rw [this.mp hve] at hal; exact absurd hal (by simp)
  · refine ⟨D0, hD0, fun a _ => ?_⟩
    by_contra hcon
    have h1 : PEqualNP.Outside.L_pcx_341_aux.Replay.value (supE z t J hz) (cstE z t J hz) a e = true := by
      by_contra h; apply hcon; exact ⟨(e, false), by simp, by simpa using h⟩
    have h2 : PEqualNP.Outside.L_pcx_341_aux.Replay.value (supE z t J hz) (cstE z t J hz) a e' = true := by
      by_contra h; apply hcon; exact ⟨(e', false), by simp, by simpa using h⟩
    have key : ∀ (f f' : GEdge (Gr' z t J hz)), f.1.1 = f'.1.1 →
        PEqualNP.Outside.L_pcx_341_aux.Replay.value (supE z t J hz) (cstE z t J hz) a f = true →
        PEqualNP.Outside.L_pcx_341_aux.Replay.value (supE z t J hz) (cstE z t J hz) a f' = true →
        oldE z t J (eU z t J hz f.1.1) (eV z t J f.1.2) = none → f.1.2 = f'.1.2 := by
      intro f f' hff hf hf' hn
      obtain ⟨c, hc1, hc2⟩ := hNT a f hf hn
      have hn' : oldE z t J (eU z t J hz f'.1.1) (eV z t J f'.1.2) = none := by
        rw [← hff, hc1, old_none_l]
      obtain ⟨c', hc1', hc2'⟩ := hNT a f' hf' hn'
      rw [← hff, hc1] at hc1'
      simp only [Sum.inr.injEq] at hc1'
      apply (eV z t J).injective
      rw [hc2, hc2', hc1']
    by_cases hn : oldE z t J (eU z t J hz e.1.1) (eV z t J e.1.2) = none
    · exact hne (key e e' hsame h1 h2 hn)
    · by_cases hn' : oldE z t J (eU z t J hz e'.1.1) (eV z t J e'.1.2) = none
      · exact hne (key e' e hsame.symm h2 h1 hn').symm
      · apply ho
        obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.mp hn
        obtain ⟨w', hw'⟩ := Option.ne_none_iff_exists'.mp hn'
        exact ⟨w, w', hw, hw'⟩

theorem hax' (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) :
    ∀ C ∈ funGraphPHP (Gr' z t J hz), ∃ D ∈ funGraphPHP (G (z+1) z t), ∀ a, ClauseSat a D →
      ClauseSat (PEqualNP.Outside.L_pcx_341_aux.Replay.value (supE z t J hz) (cstE z t J hz) a) C := by
  intro C hC
  rcases hC with (⟨i, rfl⟩ | ⟨e, e', hsame, hne, rfl⟩) | ⟨e, e', hsame, hne, rfl⟩
  · exact hax_pig z t J hz i
  · exact hax_hole z t J hz e e' hsame hne
  · exact hax_fun z t J hz e e' hsame hne

theorem reduce (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) (ht : 1 ≤ t)
    (k : ℕ) (π : List (LinKLine (GEdge (graph z t J (attA z hz) (attB z hz) hz)))) (hk : 1 ≤ k)
    (hπ : IsLinKRefutation k (funGraphPHP (graph z t J (attA z hz) (attB z hz) hz)) π) :
    ∃ τ : List (LinKLine (GEdge (G (z+1) z t))),
      IsLinKRefutation k (funGraphPHP (G (z+1) z t)) τ ∧ τ.length ≤ 2 * π.length := by
  obtain ⟨τ, hτ, hl⟩ := PEqualNP.Outside.L_pcx_341_aux.Replay.simulate k
    (funGraphPHP (Gr' z t J hz)) (funGraphPHP (G (z+1) z t)) (supE z t J hz) (cstE z t J hz) hk []
    IsLinKDerivation.nil (fun C hC => Or.inl (hax' z t J hz C hC)) π hπ
  exact ⟨τ, hτ, by simpa using hl⟩

theorem card_split4 {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (p : A ⊕ B → C ⊕ D → Bool) :
    Fintype.card {x : (A ⊕ B) × (C ⊕ D) // p x.1 x.2 = true} =
      Fintype.card {x : A × C // p (.inl x.1) (.inl x.2) = true} +
      Fintype.card {x : A × D // p (.inl x.1) (.inr x.2) = true} +
      (Fintype.card {x : B × C // p (.inr x.1) (.inl x.2) = true} +
       Fintype.card {x : B × D // p (.inr x.1) (.inr x.2) = true}) := by
  let f : {x : (A ⊕ B) × (C ⊕ D) // p x.1 x.2 = true} ≃
      ({x : A × C // p (.inl x.1) (.inl x.2) = true} ⊕
      {x : A × D // p (.inl x.1) (.inr x.2) = true}) ⊕
      ({x : B × C // p (.inr x.1) (.inl x.2) = true} ⊕
        {x : B × D // p (.inr x.1) (.inr x.2) = true}) := {
    toFun := fun ⟨(x,y),h⟩ => match x,y with
      | .inl a,.inl c => .inl (.inl ⟨(a,c),h⟩)
      | .inl a,.inr d => .inl (.inr ⟨(a,d),h⟩)
      | .inr b,.inl c => .inr (.inl ⟨(b,c),h⟩)
      | .inr b,.inr d => .inr (.inr ⟨(b,d),h⟩)
    invFun := fun x => match x with
      | .inl (.inl ⟨(a,c),h⟩) => ⟨(.inl a,.inl c),h⟩
      | .inl (.inr ⟨(a,d),h⟩) => ⟨(.inl a,.inr d),h⟩
      | .inr (.inl ⟨(b,c),h⟩) => ⟨(.inr b,.inl c),h⟩
      | .inr (.inr ⟨(b,d),h⟩) => ⟨(.inr b,.inr d),h⟩
    left_inv := by rintro ⟨⟨a|b,c|d⟩,h⟩ <;> rfl
    right_inv := by rintro ((⟨⟨a,c⟩,h⟩|⟨⟨a,d⟩,h⟩)|(⟨⟨b,c⟩,h⟩|⟨⟨b,d⟩,h⟩)) <;> rfl }
  simpa only [Fintype.card_sum] using Fintype.card_congr f

theorem card_param4 {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    (p : A → B → Bool) (f : C → A × B) (hf : Function.Injective f)
    (ok : ∀ c, p (f c).1 (f c).2 = true) (onto : ∀ a b, p a b = true → ∃ c, f c = (a,b)) :
    Fintype.card {x : A × B // p x.1 x.2 = true} = Fintype.card C := by
  symm
  apply Fintype.card_congr (Equiv.ofBijective
    (fun c => (⟨f c, ok c⟩ : {x : A × B // p x.1 x.2 = true})) ⟨?_,?_⟩)
  · intro a b h
    exact hf (congrArg Subtype.val h)
  · rintro ⟨⟨a,b⟩,h⟩
    obtain ⟨c,hc⟩ := onto a b h
    exact ⟨c, Subtype.ext hc⟩

theorem card_pos_bool (J : Bool → ℕ) :
    Fintype.card {c : Bool // 0 < J c} =
      (if 0 < J false then 1 else 0) + (if 0 < J true then 1 else 0) := by
  rw [Fintype.card_subtype, Fintype.univ_bool]
  by_cases h0 : 0 < J false <;> by_cases h1 : 0 < J true <;>
    simp [h0, h1, Finset.filter_insert, Finset.filter_singleton]

set_option maxHeartbeats 1000000 in
theorem h01' (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) : Fintype.card {x : U (z+1) z t × EP J //
    rel' z t J (attA z hz) (attB z hz) (Sum.inl x.1) (Sum.inr x.2) = true} =
    Fintype.card {c : Bool // 0 < J c} := by
  apply card_param4 (fun a b => rel' z t J (attA z hz) (attB z hz) (Sum.inl a) (Sum.inr b)) (fun c => (Sum.inl (attA z hz c.1), (⟨c.1, ⟨0, c.2⟩⟩ : EP J)))
  · rintro ⟨c, hc⟩ ⟨c', hc'⟩ h
    have := congrArg (fun x => x.2.1) h
    simp only at this
    exact Subtype.ext this
  · intro c
    simp [rel']
  · intro a b h
    simp only [rel', Sum.elim_inl, Sum.elim_inr, decide_eq_true_eq] at h
    obtain ⟨rfl, hb⟩ := h
    refine ⟨⟨b.1, by have := b.2.isLt; omega⟩, ?_⟩
    simp only [Prod.mk.injEq, true_and]
    exact ep_ext rfl hb.symm

set_option maxHeartbeats 1000000 in
theorem h10' (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) : Fintype.card {x : EP J × V (z+1) z t //
    rel' z t J (attA z hz) (attB z hz) (Sum.inr x.1) (Sum.inl x.2) = true} =
    Fintype.card {c : Bool // 0 < J c} := by
  apply card_param4 (fun a b => rel' z t J (attA z hz) (attB z hz) (Sum.inr a) (Sum.inl b)) (fun c => ((⟨c.1, ⟨J c.1 - 1, by have := c.2; omega⟩⟩ : EP J),
    Sum.inl (attB z hz c.1)))
  · rintro ⟨c, hc⟩ ⟨c', hc'⟩ h
    have := congrArg (fun x => x.1.1) h
    simp only at this
    exact Subtype.ext this
  · intro c
    have := c.2
    simp only [rel', Sum.elim_inl, Sum.elim_inr, decide_eq_true_eq, true_and, Fin.val_mk]
    omega
  · intro a b h
    simp only [rel', Sum.elim_inl, Sum.elim_inr, decide_eq_true_eq] at h
    obtain ⟨rfl, hb⟩ := h
    refine ⟨⟨a.1, by omega⟩, ?_⟩
    simp only [Prod.mk.injEq, and_true]
    exact ep_ext rfl (by simp only; omega)

set_option maxHeartbeats 1000000 in
theorem h11' (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) : Fintype.card {x : EP J × EP J //
    rel' z t J (attA z hz) (attB z hz) (Sum.inr x.1) (Sum.inr x.2) = true} =
    Fintype.card (Σ c : Bool, Fin (J c) ⊕ Fin (J c - 1)) := by
  apply card_param4 (fun a b => rel' z t J (attA z hz) (attB z hz) (Sum.inr a) (Sum.inr b)) (fun s => match s with
    | ⟨c, Sum.inl i⟩ => ((⟨c, i⟩ : EP J), (⟨c, i⟩ : EP J))
    | ⟨c, Sum.inr i⟩ => ((⟨c, ⟨i.val, by have := i.isLt; omega⟩⟩ : EP J),
        (⟨c, ⟨i.val + 1, by have := i.isLt; omega⟩⟩ : EP J)))
  · rintro ⟨c, i | i⟩ ⟨c', i' | i'⟩ h <;> simp only [Prod.mk.injEq, Sigma.mk.inj_iff] at h
    · obtain ⟨⟨rfl, h1⟩, -⟩ := h
      rw [heq_eq_eq] at h1
      rw [h1]
    · obtain ⟨⟨rfl, h1⟩, ⟨-, h2⟩⟩ := h
      have e1 := congrArg Fin.val (eq_of_heq h1)
      have e2 := congrArg Fin.val (eq_of_heq h2)
      simp only at e1 e2
      omega
    · obtain ⟨⟨rfl, h1⟩, ⟨-, h2⟩⟩ := h
      have e1 := congrArg Fin.val (eq_of_heq h1)
      have e2 := congrArg Fin.val (eq_of_heq h2)
      simp only at e1 e2
      omega
    · obtain ⟨⟨rfl, h1⟩, -⟩ := h
      have e1 := congrArg Fin.val (eq_of_heq h1)
      simp only at e1
      have : i = i' := Fin.ext e1
      rw [this]
  · rintro ⟨c, i | i⟩ <;> simp [rel']
  · rintro ⟨c, i⟩ ⟨c', i'⟩ h
    simp only [rel', Sum.elim_inr, decide_eq_true_eq] at h
    obtain ⟨rfl, h | h⟩ := h
    · refine ⟨⟨c, Sum.inl i⟩, ?_⟩
      simp only [Prod.mk.injEq, true_and]
      exact ep_ext rfl h
    · refine ⟨⟨c, Sum.inr ⟨i.val, by have := i'.isLt; omega⟩⟩, ?_⟩
      simp only [Prod.mk.injEq]
      exact ⟨by first | trivial | exact ep_ext rfl rfl, by first | trivial | exact ep_ext rfl h.symm⟩

set_option maxHeartbeats 1000000 in
theorem raw_edges (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) (ht : 1 ≤ t) (h0 : 1 ≤ J false) :
    Fintype.card {x : U' z t J × V' z t J // rel' z t J (attA z hz) (attB z hz) x.1 x.2 = true} =
      (2*t+1)*((z+1)*z + 2*(z+1)*(z-1) + 2*z*(z+1-1)) +
      (2 * J false + 1) + (if J true = 0 then 0 else 2 * J true + 1) := by
  have hc := (counts (z+1) z t hz (by omega)).2.2.2
  have h00 : Fintype.card (GEdge (G (z+1) z t)) =
      Fintype.card {x : U (z+1) z t × V (z+1) z t //
        rel' z t J (attA z hz) (attB z hz) (Sum.inl x.1) (Sum.inl x.2) = true} :=
    card_edges_relG (Fintype.equivFin _).symm (Fintype.equivFin _).symm (adj (z+1) z t)
  rw [card_split4 (rel' z t J (attA z hz) (attB z hz))]
  rw [← h00, hc, h01' z t J hz, h10' z t J hz, h11' z t J hz, card_pos_bool, Fintype.card_sigma, Fintype.sum_bool]
  simp only [Fintype.card_sum, Fintype.card_fin]
  by_cases h1 : J true = 0
  · simp only [h1, if_true]
    split_ifs <;> omega
  · simp only [h1, if_false]
    split_ifs <;> omega

theorem props (z t : ℕ) (J : Bool → ℕ) (hz : 2 ≤ z) (ht : 1 ≤ t)
    (hJ : ∀ c, J c = 0 ∨ t ≤ J c) (h0 : 1 ≤ J false) :
    let Gr := graph z t J (attA z hz) (attB z hz) hz
    Fintype.card (GEdge Gr) = (2*t+1)*((z+1)*z + 2*(z+1)*(z-1) + 2*z*(z+1-1)) +
      (2 * J false + 1) + (if J true = 0 then 0 else 2 * J true + 1) ∧
    (∀ u, 2 ≤ (Gr u).card ∧ (Gr u).card ≤ 3) ∧
    (∀ v, 2 ≤ (rightNbrs Gr v).card ∧ (rightNbrs Gr v).card ≤ 3) ∧
    (∀ color : Fin (Fintype.card (V' z t J) + 1) ⊕ Fin (Fintype.card (V' z t J)) → Bool,
      (∀ u, ∀ v ∈ Gr u, color (Sum.inl u) = color (Sum.inr v)) → ∀ x y, color x = color y) ∧
    (∀ (s : ℕ) (us : Fin (s+2) ↪ Fin (Fintype.card (V' z t J) + 1))
      (vs : Fin (s+2) ↪ Fin (Fintype.card (V' z t J))),
      (∀ i, vs i ∈ Gr (us i) ∧ vs i ∈ Gr (us (i+1))) → t ≤ s + 2) ∧
    (∀ (k : ℕ) (π : List (LinKLine (GEdge Gr))), 1 ≤ k →
      IsLinKRefutation k (funGraphPHP Gr) π →
      ∃ τ : List (LinKLine (GEdge (G (z+1) z t))),
        IsLinKRefutation k (funGraphPHP (G (z+1) z t)) τ ∧ τ.length ≤ 2 * π.length) := by
  intro Gr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h : Fintype.card (GEdge Gr) = _ := card_edges_relG (eU z t J hz) (eV z t J)
      (rel' z t J (attA z hz) (attB z hz))
    rw [h]
    exact raw_edges z t J hz ht h0
  · intro u
    have h : (Gr u).card = _ := card_left_relG (eU z t J hz) (eV z t J)
      (rel' z t J (attA z hz) (attB z hz)) u
    rw [h]
    exact raw_left z t J hz ht _
  · intro v
    have h : (rightNbrs Gr v).card = _ := card_right_relG (eU z t J hz) (eV z t J)
      (rel' z t J (attA z hz) (attB z hz)) v
    rw [h]
    exact raw_right z t J hz ht _
  · exact conn_relG _ _ _ (raw_conn z t J hz ht)
  · intro s us vs h
    obtain ⟨us', vs', h'⟩ := cycle_relG _ _ _ s us vs h
    exact raw_girth z t J hz ht hJ s us' vs' h'
  · intro k π hk hπ
    exact reduce z t J hz ht k π hk hπ

def eC (z : ℕ) : ℕ := (z+1)*z + 2*(z+1)*(z-1) + 2*z*(z+1-1)
def DD (z : ℕ) : ℕ := eC z + 2
def phi (b z : ℕ) : ℕ := DD z * ((2 * DD z)^b + 3)

theorem DD_mono {y z : ℕ} (h : y ≤ z) : DD y ≤ DD z := by
  unfold DD eC
  have h1 : y - 1 ≤ z - 1 := Nat.sub_le_sub_right h 1
  have h2 : y + 1 - 1 ≤ z + 1 - 1 := Nat.sub_le_sub_right (by omega) 1
  have h3 : (y+1)*y ≤ (z+1)*z := Nat.mul_le_mul (by omega) h
  have h4 : 2*(y+1)*(y-1) ≤ 2*(z+1)*(z-1) := Nat.mul_le_mul (Nat.mul_le_mul_left 2 (by omega)) h1
  have h5 : 2*y*(y+1-1) ≤ 2*z*(z+1-1) := Nat.mul_le_mul (Nat.mul_le_mul_left 2 h) h2
  omega

theorem phi_mono (b : ℕ) {y z : ℕ} (h : y ≤ z) : phi b y ≤ phi b z := by
  unfold phi
  have := DD_mono h
  exact Nat.mul_le_mul this (Nat.add_le_add_right (Nat.pow_le_pow_left (by omega) b) 3)

theorem le_DD (z : ℕ) : z ≤ DD z := by
  unfold DD eC
  have : z ≤ (z+1)*z := Nat.le_mul_of_pos_left z (by omega)
  omega

theorem DD_le_phi (b z : ℕ) : DD z ≤ phi b z := by
  unfold phi
  exact Nat.le_mul_of_pos_right _ (by omega)

theorem two_le_DD (z : ℕ) : 2 ≤ DD z := by unfold DD; omega

theorem ex_z (b N : ℕ) : ∃ z, N < phi b (z+1) :=
  ⟨N, lt_of_lt_of_le (Nat.lt_succ_self N) ((le_DD (N+1)).trans (DD_le_phi b (N+1)))⟩

noncomputable def zN (b N : ℕ) : ℕ := Nat.find (ex_z b N)
noncomputable def tN (b N : ℕ) : ℕ := (N - DD (zN b N)) / (2 * DD (zN b N))
noncomputable def ρN (b N : ℕ) : ℕ := N - (2 * tN b N + 1) * DD (zN b N)
noncomputable def JN (b N : ℕ) : Bool → ℕ := fun c =>
  if c then (if ρN b N % 2 = 0 then tN b N else 0)
  else ρN b N / 2 + tN b N + (if ρN b N % 2 = 0 then 0 else tN b N + 1)

noncomputable def holes (b N : ℕ) : ℕ := Fintype.card (V' (zN b N) (tN b N) (JN b N))

noncomputable def graphs (b N : ℕ) : BipGraph (holes b N + 1) (holes b N) :=
  if hz : 2 ≤ zN b N then graph (zN b N) (tN b N) (JN b N) (attA _ hz) (attB _ hz) hz
  else fun _ => ∅

theorem graphs_eq (b N : ℕ) (hz : 2 ≤ zN b N) :
    graphs b N = graph (zN b N) (tN b N) (JN b N) (attA _ hz) (attB _ hz) hz := by
  unfold graphs
  exact dif_pos hz

theorem zN_spec (b N : ℕ) : N < phi b (zN b N + 1) := Nat.find_spec (ex_z b N)

theorem zN_ge (b N Z : ℕ) (h : phi b Z ≤ N) : Z ≤ zN b N := by
  by_contra hc
  have h1 := zN_spec b N
  have h2 := phi_mono b (show zN b N + 1 ≤ Z by omega)
  omega

theorem phi_le_N (b N : ℕ) (h : phi b 1 ≤ N) : phi b (zN b N) ≤ N := by
  have hz := zN_ge b N 1 h
  obtain ⟨w, hw⟩ : ∃ w, zN b N = w + 1 := ⟨zN b N - 1, by omega⟩
  have hmin := Nat.find_min (ex_z b N) (show w < zN b N by omega)
  rw [hw]
  exact Nat.le_of_not_lt hmin

theorem t_facts (b N : ℕ) (h : DD (zN b N) ≤ N) :
    (2 * tN b N + 1) * DD (zN b N) ≤ N ∧ N < (2 * tN b N + 3) * DD (zN b N) := by
  have hD := two_le_DD (zN b N)
  have hd := Nat.div_add_mod (N - DD (zN b N)) (2 * DD (zN b N))
  have hm := Nat.mod_lt (N - DD (zN b N)) (show 0 < 2 * DD (zN b N) by omega)
  have ht : tN b N = (N - DD (zN b N)) / (2 * DD (zN b N)) := rfl
  rw [← ht] at hd
  have e1 : (2 * tN b N + 1) * DD (zN b N) = 2 * DD (zN b N) * tN b N + DD (zN b N) := by ring
  have e2 : (2 * tN b N + 3) * DD (zN b N) = 2 * DD (zN b N) * tN b N + 3 * DD (zN b N) := by
    ring
  rw [e1, e2]
  generalize 2 * DD (zN b N) * tN b N = X at *
  generalize (N - DD (zN b N)) % (2 * DD (zN b N)) = r at *
  constructor <;> omega

theorem phi_le_pow (b y : ℕ) (hb : 1 ≤ b) (hy : 12 ≤ y) : phi b y ≤ y ^ (3 * (b + 1)) := by
  have hD : DD y ≤ 6 * y ^ 2 := by
    unfold DD eC
    obtain ⟨w, rfl⟩ : ∃ w, y = w + 1 := ⟨y - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring_nf
    nlinarith
  have hX : 3 ≤ (12 * y ^ 2) ^ b := by
    calc 3 ≤ 12 * y ^ 2 := by nlinarith
      _ = (12 * y ^ 2) ^ 1 := (pow_one _).symm
      _ ≤ (12 * y ^ 2) ^ b := Nat.pow_le_pow_right (by nlinarith) hb
  have h12 : 12 ^ (b + 1) ≤ y ^ (b + 1) := Nat.pow_le_pow_left hy _
  unfold phi
  calc DD y * ((2 * DD y) ^ b + 3) ≤ (6 * y ^ 2) * ((12 * y ^ 2) ^ b + 3) := by
        apply Nat.mul_le_mul hD
        apply Nat.add_le_add_right
        apply Nat.pow_le_pow_left
        omega
    _ ≤ (6 * y ^ 2) * (2 * (12 * y ^ 2) ^ b) := Nat.mul_le_mul_left _ (by omega)
    _ = 12 ^ (b + 1) * y ^ (2 * b + 2) := by ring
    _ ≤ y ^ (b + 1) * y ^ (2 * b + 2) := Nat.mul_le_mul_right _ h12
    _ = y ^ (3 * (b + 1)) := by ring

theorem eval_mono' (p : Polynomial ℕ) {m n : ℕ} (h : m ≤ n) : p.eval m ≤ p.eval n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [Polynomial.eval_add]
    exact Nat.add_le_add hp hq
  | monomial k a =>
    simp only [Polynomial.eval_monomial]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)

structure Good (b N : ℕ) : Prop where
  hz : 12 ≤ zN b N
  ht : 1 ≤ tN b N
  hJ : ∀ c, JN b N c = 0 ∨ tN b N ≤ JN b N c
  h0 : 1 ≤ JN b N false
  edges : (2 * tN b N + 1) * ((zN b N + 1) * zN b N + 2 * (zN b N + 1) * (zN b N - 1) +
      2 * zN b N * (zN b N + 1 - 1)) + (2 * JN b N false + 1) +
      (if JN b N true = 0 then 0 else 2 * JN b N true + 1) = N
  girth : ∀ s : ℕ, tN b N ≤ s + 2 → N ^ b ≤ (2 * (s + 2)) ^ (b + 1)
  upper : N < (zN b N + 1) ^ (3 * (b + 1))

theorem good (b N : ℕ) (hb : 1 ≤ b) (hN : phi b 12 ≤ N) : Good b N := by
  have hz : 12 ≤ zN b N := zN_ge b N 12 hN
  have hphi : phi b (zN b N) ≤ N := phi_le_N b N ((phi_mono b (by omega)).trans hN)
  have hspec := zN_spec b N
  have hD2 := two_le_DD (zN b N)
  have hDN : DD (zN b N) ≤ N := (DD_le_phi b (zN b N)).trans hphi
  obtain ⟨ht1, ht2⟩ := t_facts b N hDN
  have hQ : (2 * DD (zN b N)) ^ b < 2 * tN b N := by
    have h1 : phi b (zN b N) = DD (zN b N) * ((2 * DD (zN b N)) ^ b + 3) := rfl
    have : DD (zN b N) * ((2 * DD (zN b N)) ^ b + 3) < DD (zN b N) * (2 * tN b N + 3) := by
      rw [← h1]
      calc phi b (zN b N) ≤ N := hphi
        _ < (2 * tN b N + 3) * DD (zN b N) := ht2
        _ = _ := by ring
    have := Nat.lt_of_mul_lt_mul_left this
    omega
  have hQ4 : 4 ≤ (2 * DD (zN b N)) ^ b := by
    calc 4 ≤ 2 * DD (zN b N) := by omega
      _ = (2 * DD (zN b N)) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) hb
  have hρ : ρN b N = N - (2 * tN b N + 1) * DD (zN b N) := rfl
  refine ⟨hz, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · intro c
    cases c <;> simp only [JN, Bool.false_eq_true, ite_false, ite_true] <;> split_ifs <;> omega
  · simp only [JN, Bool.false_eq_true, ite_false]
    split_ifs <;> omega
  · change (2 * tN b N + 1) * eC (zN b N) + (2 * JN b N false + 1) +
      (if JN b N true = 0 then 0 else 2 * JN b N true + 1) = N
    have hr : ρN b N + (2 * tN b N + 1) * DD (zN b N) = N := by rw [hρ]; omega
    have hX : (2 * tN b N + 1) * DD (zN b N) = (2 * tN b N + 1) * eC (zN b N) + 4 * tN b N + 2 := by
      unfold DD; ring
    simp only [JN, Bool.false_eq_true, ite_false, ite_true]
    generalize (2 * tN b N + 1) * eC (zN b N) = X at hX ⊢
    generalize (2 * tN b N + 1) * DD (zN b N) = Y at hX hr
    split_ifs <;> omega
  · intro s hs
    have hN4 : N ≤ 2 * tN b N * (2 * DD (zN b N)) := by
      calc N ≤ (2 * tN b N + 3) * DD (zN b N) := ht2.le
        _ ≤ (4 * tN b N) * DD (zN b N) := Nat.mul_le_mul_right _ (by omega)
        _ = _ := by ring
    calc N ^ b ≤ (2 * tN b N * (2 * DD (zN b N))) ^ b := Nat.pow_le_pow_left hN4 b
      _ = (2 * tN b N) ^ b * (2 * DD (zN b N)) ^ b := by rw [mul_pow]
      _ ≤ (2 * tN b N) ^ b * (2 * tN b N) := Nat.mul_le_mul_left _ hQ.le
      _ = (2 * tN b N) ^ (b + 1) := by rw [pow_succ]
      _ ≤ (2 * (s + 2)) ^ (b + 1) := Nat.pow_le_pow_left (by omega) _
  · exact lt_of_lt_of_le hspec (phi_le_pow b (zN b N + 1) hb (by omega))

theorem main : ∀ b : ℕ, 0 < b →
  ∃ B : ℕ, 2 ≤ B ∧ ∃ (holes : ℕ → ℕ)
    (graphs : ∀ N : ℕ, PEqualNP.Expanders.BipGraph (holes N+1) (holes N)),
  (∃ threshold : ℕ, ∀ N : ℕ, threshold ≤ N →
    let G := graphs N
    let L := Fin (holes N+1)
    let R := Fin (holes N)
    Fintype.card (PEqualNP.Expanders.GEdge G) = N ∧
    (∀ u : L, 2 ≤ (G u).card ∧ (G u).card ≤ 3) ∧
    (∀ v : R, 2 ≤ (PEqualNP.Expanders.rightNbrs G v).card ∧
      (PEqualNP.Expanders.rightNbrs G v).card ≤ 3) ∧
    (∀ color : L ⊕ R → Bool, (∀ u : L, ∀ v ∈ G u, color (Sum.inl u) = color (Sum.inr v)) →
      ∀ x y, color x = color y) ∧
    (∀ (s : ℕ) (us : Fin (s+2) ↪ L) (vs : Fin (s+2) ↪ R),
      (∀ i, vs i ∈ G (us i) ∧ vs i ∈ G (us (i+1))) → N^b ≤ (2*(s+2))^(b+1))) ∧
  ∀ p : Polynomial ℕ, ∃ cutoff : ℕ, ∀ N : ℕ, cutoff ≤ N →
    ∀ k : ℕ, 1 ≤ k → B^(2*k) ≤ N →
      let G := graphs N
      let proofOf := PEqualNP.ProofComplexity.IsLinKRefutation k (PEqualNP.Expanders.funGraphPHP G)
      (∃ π : List (PEqualNP.ProofComplexity.LinKLine (PEqualNP.Expanders.GEdge G)), proofOf π) ∧
      ∀ π : List (PEqualNP.ProofComplexity.LinKLine (PEqualNP.Expanders.GEdge G)),
        proofOf π → p.eval N < π.length := by
  intro b hb
  obtain ⟨B0, hB0, h204⟩ := PEqualNP.Outside.L_pcx_204
  refine ⟨B0 ^ (3 * (b + 1)), ?_, holes b, graphs b, ⟨phi b 12, ?_⟩, ?_⟩
  · calc 2 ≤ B0 := hB0
      _ = B0 ^ 1 := (pow_one _).symm
      _ ≤ B0 ^ (3 * (b + 1)) := Nat.pow_le_pow_right (by omega) (by omega)
  · intro N hN
    have g := good b N hb hN
    have hz2 : 2 ≤ zN b N := by have := g.hz; omega
    obtain ⟨hE, hL, hR, hC, hY, -⟩ := props (zN b N) (tN b N) (JN b N) hz2 g.ht g.hJ g.h0
    dsimp only
    rw [graphs_eq b N hz2]
    refine ⟨hE.trans g.edges, hL, hR, hC, ?_⟩
    intro s us vs h
    exact g.girth s (hY s us vs h)
  · intro p
    obtain ⟨n0, hn0⟩ := h204 (4 * p.comp (Polynomial.X ^ (3 * (b + 1))) + 16 * Polynomial.X ^ 2)
    refine ⟨phi b (max n0 12), fun N hN k hk hBk => ?_⟩
    have hN' : phi b 12 ≤ N := (phi_mono b (le_max_right _ _)).trans hN
    have g := good b N hb hN'
    have hzn : max n0 12 ≤ zN b N := zN_ge b N _ hN
    have hz2 : 2 ≤ zN b N := by omega
    dsimp only
    refine ⟨PEqualNP.ProofComplexity.L055 k _ _ _ hk (Nat.lt_succ_self _), ?_⟩
    have key : ∀ Gr : BipGraph (holes b N + 1) (holes b N),
        Gr = graph (zN b N) (tN b N) (JN b N) (attA _ hz2) (attB _ hz2) hz2 →
        ∀ π : List (LinKLine (GEdge Gr)), IsLinKRefutation k (funGraphPHP Gr) π →
          p.eval N < π.length := by
      intro Gr hGr π hπ
      subst hGr
      obtain ⟨-, -, -, -, -, hS⟩ := props (zN b N) (tN b N) (JN b N) hz2 g.ht g.hJ g.h0
      obtain ⟨τ1, hτ1, hl1⟩ := hS k π hk hπ
      have hup := g.upper
      obtain ⟨τ2, hτ2, hl2⟩ := simulate341 (zN b N + 1) (zN b N) _ k
        hz2 (by omega) hk τ1 hτ1
      have hB : B0 ^ (2 * k) ≤ (zN b N) := by
        have h1 : (B0 ^ (2 * k)) ^ (3 * (b + 1)) < ((zN b N) + 1) ^ (3 * (b + 1)) := by
          calc (B0 ^ (2 * k)) ^ (3 * (b + 1)) = (B0 ^ (3 * (b + 1))) ^ (2 * k) := by
                rw [← pow_mul, ← pow_mul, mul_comm]
            _ ≤ N := hBk
            _ < _ := hup
        have := (Nat.pow_lt_pow_iff_left (by omega)).mp h1
        omega
      have h3 := hn0 (zN b N) (by omega) k τ2 hk hB hτ2
      have hq : (4 * p.comp (Polynomial.X ^ (3 * (b + 1))) + 16 * Polynomial.X ^ 2 :
          Polynomial ℕ).eval (((zN b N) + 1) * (zN b N)) =
          4 * p.eval ((((zN b N) + 1) * (zN b N)) ^ (3 * (b + 1))) + 16 * (((zN b N) + 1) * (zN b N)) ^ 2 := by
        simp [Polynomial.eval_comp]
      rw [hq] at h3
      have hNle : N ≤ (((zN b N) + 1) * (zN b N)) ^ (3 * (b + 1)) :=
        hup.le.trans (Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ (by omega)) _)
      have hmono := eval_mono' p hNle
      have hpoly : 16 * ((zN b N) + 1) * (zN b N) * (((zN b N) + 1) + (zN b N)) ≤ 16 * (((zN b N) + 1) * (zN b N)) ^ 2 := by
        have : ((zN b N) + 1) + (zN b N) ≤ ((zN b N) + 1) * (zN b N) := by nlinarith
        calc 16 * ((zN b N) + 1) * (zN b N) * (((zN b N) + 1) + (zN b N)) ≤ 16 * ((zN b N) + 1) * (zN b N) * (((zN b N) + 1) * (zN b N)) :=
              Nat.mul_le_mul_left _ this
          _ = 16 * (((zN b N) + 1) * (zN b N)) ^ 2 := by ring
      have hl2' : τ2.length ≤ 2 * τ1.length + 16 * ((zN b N) + 1) * (zN b N) * (((zN b N) + 1) + (zN b N)) := hl2
      have hl1' : τ1.length ≤ 2 * π.length := hl1
      show p.eval N < π.length
      omega
    intro π hπ
    exact key _ (graphs_eq b N hz2) π hπ

end Main


end PEqualNP.Outside.L_pcx_342_aux

theorem PEqualNP.Outside.L_pcx_342 : ∀ b : ℕ, 0 < b →
  ∃ B : ℕ, 2 ≤ B ∧ ∃ (holes : ℕ → ℕ)
    (graphs : ∀ N : ℕ, PEqualNP.Expanders.BipGraph (holes N+1) (holes N)),
  (∃ threshold : ℕ, ∀ N : ℕ, threshold ≤ N →
    let G := graphs N
    let L := Fin (holes N+1)
    let R := Fin (holes N)
    Fintype.card (PEqualNP.Expanders.GEdge G) = N ∧
    (∀ u : L, 2 ≤ (G u).card ∧ (G u).card ≤ 3) ∧
    (∀ v : R, 2 ≤ (PEqualNP.Expanders.rightNbrs G v).card ∧
      (PEqualNP.Expanders.rightNbrs G v).card ≤ 3) ∧
    (∀ color : L ⊕ R → Bool, (∀ u : L, ∀ v ∈ G u, color (Sum.inl u) = color (Sum.inr v)) →
      ∀ x y, color x = color y) ∧
    (∀ (s : ℕ) (us : Fin (s+2) ↪ L) (vs : Fin (s+2) ↪ R),
      (∀ i, vs i ∈ G (us i) ∧ vs i ∈ G (us (i+1))) → N^b ≤ (2*(s+2))^(b+1))) ∧
  ∀ p : Polynomial ℕ, ∃ cutoff : ℕ, ∀ N : ℕ, cutoff ≤ N →
    ∀ k : ℕ, 1 ≤ k → B^(2*k) ≤ N →
      let G := graphs N
      let proofOf := PEqualNP.ProofComplexity.IsLinKRefutation k (PEqualNP.Expanders.funGraphPHP G)
      (∃ π : List (PEqualNP.ProofComplexity.LinKLine (PEqualNP.Expanders.GEdge G)), proofOf π) ∧
      ∀ π : List (PEqualNP.ProofComplexity.LinKLine (PEqualNP.Expanders.GEdge G)),
        proofOf π → p.eval N < π.length :=
  PEqualNP.Outside.L_pcx_342_aux.Main.main
