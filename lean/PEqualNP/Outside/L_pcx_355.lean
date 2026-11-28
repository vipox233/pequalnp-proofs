import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_pcx_352
import PEqualNP.ProofComplexity.L059
import PEqualNP.ProofComplexity.L055

namespace PEqualNP.Outside.L_pcx_355_aux

open Finset PEqualNP.ProofComplexity PEqualNP.Expanders

section AffineSim

def parity {U : Type} [DecidableEq U] (a : U → Bool) (S : Finset U) : Bool :=
  decide (Odd (S.filter (fun u => a u = true)).card)

lemma linEqSat_iff_parity {U : Type} [DecidableEq U] (a : U → Bool) (q : LinEq U) :
    LinEqSat a q ↔ parity a q.1 = q.2 := by
  unfold LinEqSat parity
  cases q.2 <;> simp

lemma nat_cast_zmod2_eq_one_iff (n : ℕ) : (n : ZMod 2) = 1 ↔ Odd n := by
  rw [ZMod.natCast_eq_one_iff_odd]

lemma sum_bool_zmod2 {U : Type} [DecidableEq U] (S : Finset U) (p : U → Prop) [DecidablePred p] :
    (∑ u ∈ S, if p u then (1 : ZMod 2) else 0) = ((S.filter p).card : ZMod 2) := by
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul, mul_one]

lemma parity_eq_true_iff_sum {U : Type} [DecidableEq U] (a : U → Bool) (S : Finset U) :
    parity a S = true ↔ (∑ u ∈ S, if a u = true then (1 : ZMod 2) else 0) = 1 := by
  rw [sum_bool_zmod2, nat_cast_zmod2_eq_one_iff]
  simp [parity]

lemma zmod2_bool_xor (b c : Bool) :
    (if xor b c = true then (1 : ZMod 2) else 0) =
    (if b = true then 1 else 0) + (if c = true then 1 else 0) := by
  cases b <;> cases c <;> decide

lemma zmod2_eq_iff_bool (b c : Bool) :
    b = c ↔ (if b = true then (1 : ZMod 2) else 0) = (if c = true then 1 else 0) := by
  cases b <;> cases c <;> decide

lemma parity_zmod2 {U : Type} [DecidableEq U] (a : U → Bool) (S : Finset U) :
    (if parity a S = true then (1 : ZMod 2) else 0) =
    ∑ u ∈ S, if a u = true then (1 : ZMod 2) else 0 := by
  have h1 := parity_eq_true_iff_sum a S
  cases hp : parity a S
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hne : (∑ u ∈ S, if a u = true then (1 : ZMod 2) else 0) ≠ 1 := by
      intro h; exact absurd (h1.mpr h) (by simp [hp])
    generalize (∑ u ∈ S, if a u = true then (1 : ZMod 2) else 0) = z at hne ⊢
    fin_cases z
    · rfl
    · exact absurd rfl hne
  · simp only [↓reduceIte]
    exact (h1.mp hp).symm

lemma parity_insert {U : Type} [DecidableEq U] (a : U → Bool) (S : Finset U) (u : U) (hu : u ∉ S) :
    parity a (insert u S) = xor (a u) (parity a S) := by
  rw [zmod2_eq_iff_bool, parity_zmod2, Finset.sum_insert hu, zmod2_bool_xor, parity_zmod2]

lemma parity_singleton {U : Type} [DecidableEq U] (a : U → Bool) (u : U) :
    parity a {u} = a u := by
  rw [zmod2_eq_iff_bool, parity_zmod2, Finset.sum_singleton]

lemma parity_empty {U : Type} [DecidableEq U] (a : U → Bool) :
    parity a ∅ = false := by
  simp [parity]

def substEq {V U : Type} [Fintype U] [DecidableEq V] [DecidableEq U]
    (σ : V → LinEq U) (q : LinEq V) : LinEq U :=
  (Finset.univ.filter (fun u => Odd (q.1.filter (fun v => u ∈ (σ v).1)).card),
   xor q.2 (decide (Odd (q.1.filter (fun v => (σ v).2 = true)).card)))

def substAssign {V U : Type} [DecidableEq U] (σ : V → LinEq U) (a : U → Bool) (v : V) : Bool :=
  xor (parity a (σ v).1) (σ v).2

lemma substEq_neg {V U : Type} [Fintype U] [DecidableEq V] [DecidableEq U]
    (σ : V → LinEq U) (q : LinEq V) :
    substEq σ (negLinEq q) = negLinEq (substEq σ q) := by
  rcases q with ⟨A, b⟩
  refine Prod.ext rfl ?_
  dsimp only [substEq, negLinEq]
  cases b <;> simp only [Bool.not_true, Bool.not_false, Bool.true_xor, Bool.false_xor, Bool.not_not]
  · exact congrArg Bool.not (decide_eq_decide.mpr Iff.rfl)
  · exact decide_eq_decide.mpr Iff.rfl

lemma substEq_sat {V U : Type} [Fintype U] [DecidableEq V] [DecidableEq U]
    (σ : V → LinEq U) (a : U → Bool) (q : LinEq V) :
    LinEqSat a (substEq σ q) ↔ LinEqSat (substAssign σ a) q := by
  rw [linEqSat_iff_parity, linEqSat_iff_parity,
      zmod2_eq_iff_bool (parity a (substEq σ q).1) (substEq σ q).2,
      zmod2_eq_iff_bool (parity (substAssign σ a) q.1) q.2]
  rcases q with ⟨A, b⟩
  simp only [substEq, parity_zmod2]
  have h1 : (∑ u ∈ Finset.univ.filter (fun u => Odd (A.filter (fun v => u ∈ (σ v).1)).card),
      if a u = true then (1 : ZMod 2) else 0) =
      ∑ v ∈ A, if parity a (σ v).1 = true then (1 : ZMod 2) else 0 := by
    have hL : (∑ u ∈ Finset.univ.filter (fun u => Odd (A.filter (fun v => u ∈ (σ v).1)).card),
        if a u = true then (1 : ZMod 2) else 0) =
        ∑ u : U, (if a u = true then (1 : ZMod 2) else 0) *
          ((A.filter (fun v => u ∈ (σ v).1)).card : ZMod 2) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      by_cases hodd : Odd (A.filter (fun v => u ∈ (σ v).1)).card
      · have hcast : ((A.filter (fun v => u ∈ (σ v).1)).card : ZMod 2) = 1 :=
          (nat_cast_zmod2_eq_one_iff _).mpr hodd
        simp [hodd, hcast]
      · have hcast : ((A.filter (fun v => u ∈ (σ v).1)).card : ZMod 2) = 0 := by
          have hne : ((A.filter (fun v => u ∈ (σ v).1)).card : ZMod 2) ≠ 1 :=
            fun h => hodd ((nat_cast_zmod2_eq_one_iff _).mp h)
          generalize ((A.filter (fun v => u ∈ (σ v).1)).card : ZMod 2) = z at hne ⊢
          fin_cases z
          · rfl
          · exact absurd rfl hne
        simp [hodd, hcast]
    rw [hL]
    have hR : ∀ u : U, (if a u = true then (1 : ZMod 2) else 0) *
        ((A.filter (fun v => u ∈ (σ v).1)).card : ZMod 2) =
        ∑ v ∈ A, if u ∈ (σ v).1 then (if a u = true then (1 : ZMod 2) else 0) else 0 := by
      intro u
      rw [← sum_bool_zmod2, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      split_ifs <;> simp
    simp_rw [hR]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    rw [parity_zmod2, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext u; simp
  have h2 : (∑ v ∈ A, if substAssign σ a v = true then (1 : ZMod 2) else 0) =
      (∑ v ∈ A, if parity a (σ v).1 = true then (1 : ZMod 2) else 0) +
      (∑ v ∈ A, if (σ v).2 = true then (1 : ZMod 2) else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    exact zmod2_bool_xor _ _
  have h3 : (if decide (Odd (A.filter (fun v => (σ v).2 = true)).card) = true then (1 : ZMod 2) else 0) =
      ∑ v ∈ A, if (σ v).2 = true then (1 : ZMod 2) else 0 := by
    rw [sum_bool_zmod2]
    by_cases hodd : Odd (A.filter (fun v => (σ v).2 = true)).card
    · simp [hodd, (nat_cast_zmod2_eq_one_iff _).mpr hodd]
    · have hcast : ((A.filter (fun v => (σ v).2 = true)).card : ZMod 2) = 0 := by
        have hne : ((A.filter (fun v => (σ v).2 = true)).card : ZMod 2) ≠ 1 :=
          fun h => hodd ((nat_cast_zmod2_eq_one_iff _).mp h)
        generalize ((A.filter (fun v => (σ v).2 = true)).card : ZMod 2) = z at hne ⊢
        fin_cases z
        · rfl
        · exact absurd rfl hne
      simp [hodd, hcast]
  rw [h1, h2, zmod2_bool_xor, h3]
  generalize (∑ v ∈ A, if parity a (σ v).1 = true then (1 : ZMod 2) else 0) = x
  generalize (∑ v ∈ A, if (σ v).2 = true then (1 : ZMod 2) else 0) = y
  generalize (if b = true then (1 : ZMod 2) else 0) = z
  have h2y : y + y = 0 := CharTwo.add_self_eq_zero y
  constructor <;> intro h
  · calc x + y = (z + y) + y := by rw [h]
      _ = z + (y + y) := by ring
      _ = z := by rw [h2y, add_zero]
  · calc x = x + (y + y) := by rw [h2y, add_zero]
      _ = (x + y) + y := by ring
      _ = z + y := by rw [h]

lemma substEq_single {V U : Type} [Fintype U] [DecidableEq V] [DecidableEq U]
    (σ : V → LinEq U) (v : V) (b : Bool) :
    substEq σ ({v}, b) = ((σ v).1, xor b (σ v).2) := by
  simp only [substEq, Prod.mk.injEq]
  constructor
  · ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hu : u ∈ (σ v).1 <;> simp [Finset.filter_singleton, hu]
  · cases h2 : (σ v).2 <;> simp [Finset.filter_singleton, h2]

def substTerm {V U : Type} [Fintype U] [DecidableEq V] [DecidableEq U]
    (σ : V → LinEq U) (T : LinTerm V) : LinTerm U :=
  T.image (substEq σ)

def substLine {V U : Type} [Fintype U] [DecidableEq V] [DecidableEq U]
    (σ : V → LinEq U) (L : LinKLine V) : LinKLine U :=
  L.image (substTerm σ)

lemma substTerm_sat {V U : Type} [Fintype U] [DecidableEq V] [DecidableEq U]
    (σ : V → LinEq U) (a : U → Bool) (T : LinTerm V) :
    LinTermSat a (substTerm σ T) ↔ LinTermSat (substAssign σ a) T := by
  simp only [LinTermSat, substTerm, Finset.mem_image, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, substEq_sat]

lemma substLine_sat {V U : Type} [Fintype U] [DecidableEq V] [DecidableEq U]
    (σ : V → LinEq U) (a : U → Bool) (L : LinKLine V) :
    LinKLineSat a (substLine σ L) ↔ LinKLineSat (substAssign σ a) L := by
  simp only [LinKLineSat, substLine, Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨T, hT, rfl⟩, hsat⟩
    exact ⟨T, hT, (substTerm_sat σ a T).mp hsat⟩
  · rintro ⟨T, hT, hsat⟩
    exact ⟨substTerm σ T, ⟨T, hT, rfl⟩, (substTerm_sat σ a T).mpr hsat⟩

lemma substTerm_card_le {V U : Type} [Fintype U] [DecidableEq V] [DecidableEq U]
    (σ : V → LinEq U) (T : LinTerm V) : (substTerm σ T).card ≤ T.card :=
  Finset.card_image_le

lemma substLine_width {V U : Type} [Fintype U] [DecidableEq V] [DecidableEq U]
    (σ : V → LinEq U) (k : ℕ) (L : LinKLine V) (hL : ∀ T ∈ L, T.card ≤ k) :
    ∀ S ∈ substLine σ L, S.card ≤ k := by
  intro S hS
  rcases Finset.mem_image.mp hS with ⟨T, hT, rfl⟩
  exact le_trans (substTerm_card_le σ T) (hL T hT)

lemma isLinKWeakening_of_subset {U : Type} {L M : LinKLine U} (h : L ⊆ M) :
    IsLinKWeakening L M := by
  intro T hT
  left
  exact ⟨T, h hT, fun _ ha => ha⟩

lemma isLinKWeakening_one_sem {U : Type} {L M : LinKLine U}
    (h1 : ∀ S ∈ M, S.card = 1)
    (hsem : ∀ a : U → Bool, LinKLineSat a L → LinKLineSat a M) :
    IsLinKWeakening L M := by
  intro T hT
  right
  intro a ha
  rcases hsem a ⟨T, hT, ha⟩ with ⟨S, hSM, hSsat⟩
  rcases Finset.card_eq_one.mp (h1 S hSM) with ⟨q, rfl⟩
  exact ⟨q, hSM, hSsat q (Finset.mem_singleton_self q)⟩

lemma substLine_weakening {V U : Type} [Fintype U] [DecidableEq V] [DecidableEq U]
    (σ : V → LinEq U) {L M : LinKLine V} (hw : IsLinKWeakening L M) :
    IsLinKWeakening (substLine σ L) (substLine σ M) := by
  intro T' hT'
  rcases Finset.mem_image.mp hT' with ⟨T, hT, rfl⟩
  rcases hw T hT with ⟨S, hSM, himp⟩ | hdisj
  · left
    refine ⟨substTerm σ S, Finset.mem_image_of_mem _ hSM, fun a ha => ?_⟩
    exact (substTerm_sat σ a S).mpr (himp (substAssign σ a) ((substTerm_sat σ a T).mp ha))
  · right
    intro a ha
    rcases hdisj (substAssign σ a) ((substTerm_sat σ a T).mp ha) with ⟨q, hqM, hqsat⟩
    refine ⟨substEq σ q, ?_, (substEq_sat σ a q).mpr hqsat⟩
    have heq : ({substEq σ q} : LinTerm U) = substTerm σ {q} := by simp [substTerm]
    rw [heq]
    exact Finset.mem_image_of_mem _ hqM

lemma substLine_of_clause {V U : Type} [Fintype U] [DecidableEq V] [DecidableEq U]
    (σ : V → LinEq U) (C : Clause V) :
    substLine σ (linKOfClause C) = C.image (fun l => ({((σ l.1).1, xor l.2 (σ l.1).2)} : LinTerm U)) := by
  ext S
  simp only [substLine, linKOfClause, linOfClause, Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨_, ⟨l, hlC, rfl⟩, rfl⟩, rfl⟩
    refine ⟨l, hlC, ?_⟩
    simp [substTerm, substEq_single]
  · rintro ⟨l, hlC, rfl⟩
    refine ⟨{({l.1}, l.2)}, ⟨({l.1}, l.2), ⟨l, hlC, rfl⟩, rfl⟩, ?_⟩
    simp [substTerm, substEq_single]

lemma linKOfClause_card_one {U : Type} [DecidableEq U] (C : Clause U) :
    ∀ T ∈ linKOfClause C, T.card = 1 := by
  intro T hT
  rcases Finset.mem_image.mp hT with ⟨q, _, rfl⟩
  simp

lemma substLine_clause_card_one {V U : Type} [Fintype U] [DecidableEq V] [DecidableEq U]
    (σ : V → LinEq U) (C : Clause V) :
    ∀ T ∈ substLine σ (linKOfClause C), T.card = 1 := by
  intro T hT
  rw [substLine_of_clause] at hT
  rcases Finset.mem_image.mp hT with ⟨l, _, rfl⟩
  simp

lemma linKOfClause_sat_iff {U : Type} [DecidableEq U] (a : U → Bool) (C : Clause U) :
    LinKLineSat a (linKOfClause C) ↔ ∃ l ∈ C, a l.1 = l.2 := by
  simp only [LinKLineSat, linKOfClause, linOfClause, Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨_, ⟨l, hlC, rfl⟩, rfl⟩, hsat⟩
    refine ⟨l, hlC, ?_⟩
    have hq := hsat ({l.1}, l.2) (Finset.mem_singleton_self _)
    rwa [linEqSat_iff_parity, parity_singleton] at hq
  · rintro ⟨l, hlC, hl⟩
    refine ⟨{({l.1}, l.2)}, ⟨({l.1}, l.2), ⟨l, hlC, rfl⟩, rfl⟩, ?_⟩
    intro q hq
    rw [Finset.mem_singleton.mp hq, linEqSat_iff_parity, parity_singleton]
    exact hl

lemma affine_sim {V U : Type} [Fintype U] [DecidableEq V] [DecidableEq U]
    (k M : ℕ) (hk : 1 ≤ k) (F₀ : Set (Clause U)) (F₁ : Set (Clause V))
    (A₀ : Clause U) (hA₀ : A₀ ∈ F₀) (σ : V → LinEq U)
    (hax : ∀ C ∈ F₁, ∀ π₀,
      IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' F₀) π₀ →
      linKOfClause A₀ ∈ π₀ →
      ∃ π', IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' F₀) π' ∧
        (∀ L ∈ π₀, L ∈ π') ∧ substLine σ (linKOfClause C) ∈ π' ∧
        π'.length ≤ π₀.length + M)
    (π : List (LinKLine V)) (hπ : IsLinKRefutation k F₁ π) :
    ∃ π₀ : List (LinKLine U),
      IsLinKRefutation k F₀ π₀ ∧ π₀.length ≤ 1 + max M 2 * π.length := by
  rcases hπ with ⟨hder, hempty⟩
  suffices ∃ π₀ : List (LinKLine U),
      IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' F₀) π₀ ∧
      linKOfClause A₀ ∈ π₀ ∧
      (∀ L ∈ π, substLine σ L ∈ π₀) ∧
      π₀.length ≤ 1 + max M 2 * π.length by
    rcases this with ⟨π₀, hder0, _, hmem0, hlen0⟩
    refine ⟨π₀, ⟨hder0, ?_⟩, hlen0⟩
    have he := hmem0 ∅ hempty
    simpa [substLine] using he
  clear hempty
  induction hder with
  | nil =>
    refine ⟨[linKOfClause A₀], ?_, by simp, by simp, by simp⟩
    exact IsLinKDerivation.ax IsLinKDerivation.nil ⟨A₀, hA₀, rfl⟩
      (fun T hT => by rw [linKOfClause_card_one A₀ T hT]; exact hk)
  | @ax π C hder hCF hCw ih =>
    rcases ih with ⟨π₀, hder0, hA0in, hmem0, hlen0⟩
    rcases hCF with ⟨Cl, hClF, rfl⟩
    rcases hax Cl hClF π₀ hder0 hA0in with ⟨π', hder', hsub', hCin', hlen'⟩
    refine ⟨π', hder', hsub' _ hA0in, ?_, ?_⟩
    · intro L hL
      rcases List.mem_cons.mp hL with rfl | hLπ
      · exact hCin'
      · exact hsub' _ (hmem0 L hLπ)
    · simp only [List.length_cons]
      have hM : M ≤ max M 2 := le_max_left _ _
      have hmul : max M 2 * (π.length + 1) = max M 2 * π.length + max M 2 := by ring
      omega
  | @cut π C D R hder hC hD hcut hRw ih =>
    rcases ih with ⟨π₀, hder0, hA0in, hmem0, hlen0⟩
    rcases hcut with ⟨T, hTC, hTD, rfl⟩
    let T' := substTerm σ T
    let C' := substLine σ C
    let D' := substLine σ D
    let R' := C'.erase T' ∪ (D' \ T'.image (fun e => ({negLinEq e} : LinTerm U)))
    have hT'C' : T' ∈ C' := Finset.mem_image_of_mem _ hTC
    have hT'D' : ∀ e' ∈ T', ({negLinEq e'} : LinTerm U) ∈ D' := by
      intro e' he'
      rcases Finset.mem_image.mp he' with ⟨e, heT, rfl⟩
      have h1 : ({negLinEq (substEq σ e)} : LinTerm U) = substTerm σ {negLinEq e} := by
        simp [substTerm, substEq_neg]
      rw [h1]
      exact Finset.mem_image_of_mem _ (hTD e heT)
    have hR'sub : R' ⊆ substLine σ (C.erase T ∪ (D \ T.image (fun e => ({negLinEq e} : LinTerm V)))) := by
      intro S hS
      rcases Finset.mem_union.mp hS with hSL | hSR
      · rcases Finset.mem_erase.mp hSL with ⟨hST', hSC'⟩
        rcases Finset.mem_image.mp hSC' with ⟨T₁, hT₁C, rfl⟩
        have hne : T₁ ≠ T := fun h => hST' (by rw [h])
        exact Finset.mem_image_of_mem _ (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hT₁C⟩))
      · rcases Finset.mem_sdiff.mp hSR with ⟨hSD', hSnot⟩
        rcases Finset.mem_image.mp hSD' with ⟨T₁, hT₁D, rfl⟩
        have hnot1 : T₁ ∉ T.image (fun e => ({negLinEq e} : LinTerm V)) := by
          intro hmem
          rcases Finset.mem_image.mp hmem with ⟨e, heT, rfl⟩
          apply hSnot
          refine Finset.mem_image.mpr ⟨substEq σ e, Finset.mem_image_of_mem _ heT, ?_⟩
          simp [substTerm, substEq_neg]
        exact Finset.mem_image_of_mem _ (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hT₁D, hnot1⟩))
    have hRsubW : ∀ S ∈ substLine σ (C.erase T ∪ (D \ T.image (fun e => ({negLinEq e} : LinTerm V)))),
        S.card ≤ k := substLine_width σ k _ hRw
    have hR'W : ∀ S ∈ R', S.card ≤ k := fun S hS => hRsubW S (hR'sub hS)
    have hder1 := IsLinKDerivation.cut hder0 (hmem0 C hC) (hmem0 D hD) ⟨T', hT'C', hT'D', rfl⟩ hR'W
    have hder2 := IsLinKDerivation.weak hder1 List.mem_cons_self (isLinKWeakening_of_subset hR'sub) hRsubW
    refine ⟨_ :: R' :: π₀, hder2, by simp [hA0in], ?_, ?_⟩
    · intro L hL
      rcases List.mem_cons.mp hL with rfl | hLπ
      · simp
      · simp [hmem0 L hLπ]
    · simp only [List.length_cons]
      have h2 : 2 ≤ max M 2 := le_max_right _ _
      have hmul : max M 2 * (π.length + 1) = max M 2 * π.length + max M 2 := by ring
      omega
  | @andIntro π C D R hder hC hD hand hRw ih =>
    rcases ih with ⟨π₀, hder0, hA0in, hmem0, hlen0⟩
    rcases hand with ⟨T₁, T₂, hT₁C, hT₂D, rfl⟩
    let T₁' := substTerm σ T₁
    let T₂' := substTerm σ T₂
    let C' := substLine σ C
    let D' := substLine σ D
    let R' := (C'.erase T₁' ∪ D'.erase T₂') ∪ {T₁' ∪ T₂'}
    have hR'sub : R' ⊆ substLine σ ((C.erase T₁ ∪ D.erase T₂) ∪ {T₁ ∪ T₂}) := by
      intro S hS
      rcases Finset.mem_union.mp hS with hSL | hSR
      · rcases Finset.mem_union.mp hSL with hSC | hSD
        · rcases Finset.mem_erase.mp hSC with ⟨hne', hSC'⟩
          rcases Finset.mem_image.mp hSC' with ⟨U₁, hU₁C, rfl⟩
          have hne : U₁ ≠ T₁ := fun h => hne' (by rw [h])
          exact Finset.mem_image_of_mem _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne, hU₁C⟩)))
        · rcases Finset.mem_erase.mp hSD with ⟨hne', hSD'⟩
          rcases Finset.mem_image.mp hSD' with ⟨U₂, hU₂D, rfl⟩
          have hne : U₂ ≠ T₂ := fun h => hne' (by rw [h])
          exact Finset.mem_image_of_mem _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne, hU₂D⟩)))
      · rw [Finset.mem_singleton.mp hSR]
        have hun : T₁' ∪ T₂' = substTerm σ (T₁ ∪ T₂) := by simp [T₁', T₂', substTerm, Finset.image_union]
        rw [hun]
        exact Finset.mem_image_of_mem _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
    have hRsubW := substLine_width σ k _ hRw
    have hR'W : ∀ S ∈ R', S.card ≤ k := fun S hS => hRsubW S (hR'sub hS)
    have hder1 := IsLinKDerivation.andIntro hder0 (hmem0 C hC) (hmem0 D hD)
      ⟨T₁', T₂', Finset.mem_image_of_mem _ hT₁C, Finset.mem_image_of_mem _ hT₂D, rfl⟩ hR'W
    have hder2 := IsLinKDerivation.weak hder1 List.mem_cons_self (isLinKWeakening_of_subset hR'sub) hRsubW
    refine ⟨_ :: R' :: π₀, hder2, by simp [hA0in], ?_, ?_⟩
    · intro L hL
      rcases List.mem_cons.mp hL with rfl | hLπ
      · simp
      · simp [hmem0 L hLπ]
    · simp only [List.length_cons]
      have h2 : 2 ≤ max M 2 := le_max_right _ _
      have hmul : max M 2 * (π.length + 1) = max M 2 * π.length + max M 2 := by ring
      omega
  | @weak π C D hder hC hw hDw ih =>
    rcases ih with ⟨π₀, hder0, hA0in, hmem0, hlen0⟩
    have hder1 := IsLinKDerivation.weak hder0 (hmem0 C hC) (substLine_weakening σ hw)
      (substLine_width σ k D hDw)
    refine ⟨substLine σ D :: π₀, hder1, by simp [hA0in], ?_, ?_⟩
    · intro L hL
      rcases List.mem_cons.mp hL with rfl | hLπ
      · simp
      · simp [hmem0 L hLπ]
    · simp only [List.length_cons]
      have h2 : 1 ≤ max M 2 := le_trans (by omega) (le_max_right M 2)
      have hmul : max M 2 * (π.length + 1) = max M 2 * π.length + max M 2 := by ring
      omega

def prefSet {U : Type} [DecidableEq U] {d : ℕ} (e : Fin d → U) (t : ℕ) : Finset U :=
  (Finset.univ.filter (fun i : Fin d => i.val ≤ t)).image e

lemma prefSet_zero {U : Type} [DecidableEq U] {d : ℕ} (hd : 0 < d) (e : Fin d → U) :
    prefSet e 0 = {e ⟨0, hd⟩} := by
  ext u
  simp only [prefSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have : i = ⟨0, hd⟩ := Fin.ext (by (try dsimp); omega)
    rw [this]
  · rintro rfl
    exact ⟨⟨0, hd⟩, le_rfl, rfl⟩

lemma prefSet_succ {U : Type} [DecidableEq U] {d : ℕ} (e : Fin d → U) (t : ℕ) (ht : t + 1 < d) :
    prefSet e (t + 1) = insert (e ⟨t + 1, ht⟩) (prefSet e t) := by
  ext u
  simp only [prefSet, Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases heq : i.val = t + 1
    · left; congr 1; exact Fin.ext heq
    · right; exact ⟨i, by omega, rfl⟩
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact ⟨⟨t + 1, ht⟩, le_rfl, rfl⟩
    · exact ⟨i, by omega, rfl⟩

lemma not_mem_prefSet {U : Type} [DecidableEq U] {d : ℕ} {e : Fin d → U} (hinj : Function.Injective e)
    (t : ℕ) (ht : t + 1 < d) : e ⟨t + 1, ht⟩ ∉ prefSet e t := by
  intro hmem
  rcases Finset.mem_image.mp hmem with ⟨i, hi, heq⟩
  have hi' := (Finset.mem_filter.mp hi).2
  have := congrArg Fin.val (hinj heq)
  dsimp only at this
  omega

lemma derive_cut_one {U : Type} [DecidableEq U] {k : ℕ} (hk : 1 ≤ k) {F₀ : Set (Clause U)}
    {π₀ : List (LinKLine U)} (hder : IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' F₀) π₀)
    {L₁ L₂ R : LinKLine U} (h1 : L₁ ∈ π₀) (h2 : L₂ ∈ π₀) (q : LinEq U)
    (hq1 : ({q} : LinTerm U) ∈ L₁) (hq2 : ({negLinEq q} : LinTerm U) ∈ L₂)
    (hR1 : ∀ T ∈ R, T.card = 1)
    (hRsub : L₁.erase {q} ∪ L₂.erase {negLinEq q} ⊆ R) :
    ∃ π', IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' F₀) π' ∧
      (∀ L ∈ π₀, L ∈ π') ∧ R ∈ π' ∧ π'.length ≤ π₀.length + 2 := by
  let R₀ := L₁.erase {q} ∪ (L₂ \ ({q} : LinTerm U).image (fun e => ({negLinEq e} : LinTerm U)))
  have hR₀eq : R₀ = L₁.erase {q} ∪ L₂.erase {negLinEq q} := by
    simp [R₀, Finset.sdiff_singleton_eq_erase]
  have hR₀sub : R₀ ⊆ R := hR₀eq ▸ hRsub
  have hR₀w : ∀ T ∈ R₀, T.card ≤ k := fun T hT => by rw [hR1 T (hR₀sub hT)]; exact hk
  have hRw : ∀ T ∈ R, T.card ≤ k := fun T hT => by rw [hR1 T hT]; exact hk
  have hcut : IsLinKCut L₁ L₂ R₀ := ⟨{q}, hq1, fun e he => by
    rw [Finset.mem_singleton.mp he]; exact hq2, rfl⟩
  have hd1 := IsLinKDerivation.cut hder h1 h2 hcut hR₀w
  have hd2 := IsLinKDerivation.weak hd1 (by simp) (isLinKWeakening_of_subset hR₀sub) hRw
  exact ⟨R :: R₀ :: π₀, hd2, fun L hL => by simp [hL], by simp, by simp⟩

lemma derive_amo_prefix {U : Type} [DecidableEq U] {k d : ℕ} (hk : 1 ≤ k) (F₀ : Set (Clause U))
    {e : Fin d → U} (hinj : Function.Injective e)
    (hamo : ∀ a b : Fin d, a ≠ b → ({(e a, false), (e b, false)} : Clause U) ∈ F₀)
    (j : Fin d) (t : ℕ) (htj : t < j.val) :
    ∀ π₀, IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' F₀) π₀ →
      ∃ π', IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' F₀) π' ∧
        (∀ L ∈ π₀, L ∈ π') ∧
        ({{(prefSet e t, false)}, {({e j}, false)}} : LinKLine U) ∈ π' ∧
        π'.length ≤ π₀.length + 4 * (t + 1) := by
  induction t with
  | zero =>
    intro π₀ hder
    have h0lt : 0 < d := lt_of_le_of_lt (Nat.zero_le _) j.isLt
    have hne : (⟨0, h0lt⟩ : Fin d) ≠ j := fun h => by have := congrArg Fin.val h; dsimp at this; omega
    let Cl : Clause U := {(e ⟨0, h0lt⟩, false), (e j, false)}
    have hCl : Cl ∈ F₀ := hamo ⟨0, h0lt⟩ j hne
    have hline : linKOfClause Cl = {{(prefSet e 0, false)}, {({e j}, false)}} := by
      rw [prefSet_zero h0lt e]
      simp [Cl, linKOfClause, linOfClause]
    have hd1 := IsLinKDerivation.ax hder ⟨Cl, hCl, rfl⟩ (fun T hT => by
      rw [linKOfClause_card_one Cl T hT]; exact hk)
    dsimp only at hd1
    rw [hline] at hd1
    exact ⟨_ :: π₀, hd1, fun L hL => by simp [hL], by simp, by simp⟩
  | succ t ih =>
    intro π₀ hder
    rcases ih (by omega) π₀ hder with ⟨π₁, hder1, hsub1, hLt, hlen1⟩
    have ht1d : t + 1 < d := lt_trans htj j.isLt
    have hne : (⟨t + 1, ht1d⟩ : Fin d) ≠ j := fun h => by have := congrArg Fin.val h; dsimp at this; omega
    let Cl : Clause U := {(e ⟨t + 1, ht1d⟩, false), (e j, false)}
    have hCl : Cl ∈ F₀ := hamo ⟨t + 1, ht1d⟩ j hne
    have hAline : linKOfClause Cl = {{({e ⟨t + 1, ht1d⟩}, false)}, {({e j}, false)}} := by
      simp [Cl, linKOfClause, linOfClause]
    have hder2 := IsLinKDerivation.ax hder1 ⟨Cl, hCl, rfl⟩ (fun T hT => by
      rw [linKOfClause_card_one Cl T hT]; exact hk)
    dsimp only at hder2
    rw [hAline] at hder2
    let W : LinKLine U := {{(prefSet e (t + 1), false)}, {({e ⟨t + 1, ht1d⟩}, true)}, {({e j}, false)}}
    have hW1 : ∀ S ∈ W, S.card = 1 := by
      intro S hS; simp only [W, Finset.mem_insert, Finset.mem_singleton] at hS
      rcases hS with rfl | rfl | rfl <;> simp
    have hweak : IsLinKWeakening {{(prefSet e t, false)}, {({e j}, false)}} W := by
      apply isLinKWeakening_one_sem hW1
      intro a hsat
      rcases hsat with ⟨T, hT, hTsat⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl
      · have hp : parity a (prefSet e t) = false := by
          have := hTsat _ (Finset.mem_singleton_self _)
          rwa [linEqSat_iff_parity] at this
        cases he : a (e ⟨t + 1, ht1d⟩)
        · refine ⟨{(prefSet e (t + 1), false)}, by simp [W], fun q hq => ?_⟩
          rw [Finset.mem_singleton.mp hq, linEqSat_iff_parity,
            prefSet_succ e t ht1d, parity_insert a _ _ (not_mem_prefSet hinj t ht1d), he, hp]
          rfl
        · refine ⟨{({e ⟨t + 1, ht1d⟩}, true)}, by simp [W], fun q hq => ?_⟩
          rw [Finset.mem_singleton.mp hq, linEqSat_iff_parity, parity_singleton, he]
      · exact ⟨{({e j}, false)}, by simp [W], hTsat⟩
    have hder3 := IsLinKDerivation.weak hder2 (by simp [hLt]) hweak
      (fun T hT => by rw [hW1 T hT]; exact hk)
    let R : LinKLine U := {{(prefSet e (t + 1), false)}, {({e j}, false)}}
    have hR1 : ∀ S ∈ R, S.card = 1 := by
      intro S hS; simp only [R, Finset.mem_insert, Finset.mem_singleton] at hS
      rcases hS with rfl | rfl <;> simp
    have hRsub : W.erase {({e ⟨t + 1, ht1d⟩}, true)} ∪
        ({{({e ⟨t + 1, ht1d⟩}, false)}, {({e j}, false)}} : LinKLine U).erase {negLinEq ({e ⟨t + 1, ht1d⟩}, true)} ⊆ R := by
      intro S hS
      simp only [W, R, negLinEq, Bool.not_true, Finset.mem_union, Finset.mem_erase,
        Finset.mem_insert, Finset.mem_singleton] at hS ⊢
      rcases hS with ⟨hne1, rfl | rfl | rfl⟩ | ⟨hne2, rfl | rfl⟩
      · left; rfl
      · exact absurd rfl hne1
      · right; rfl
      · exact absurd rfl hne2
      · right; rfl
    rcases derive_cut_one hk hder3 (by simp) (by simp) ({e ⟨t + 1, ht1d⟩}, true)
      (by simp [W]) (by simp [negLinEq]) hR1 hRsub with ⟨π₄, hder4, hsub4, hRin4, hlen4⟩
    refine ⟨π₄, hder4, fun L hL => hsub4 _ (by simp [hsub1 L hL]), hRin4, ?_⟩
    simp only [List.length_cons] at hlen4
    omega

lemma derive_alo_prefix {U : Type} [DecidableEq U] {k d : ℕ} (hk : 1 ≤ k) (hd : 2 ≤ d)
    (F₀ : Set (Clause U)) {e : Fin d → U} (hinj : Function.Injective e)
    (hamo : ∀ a b : Fin d, a ≠ b → ({(e a, false), (e b, false)} : Clause U) ∈ F₀)
    (halo : (Finset.univ.image (fun i : Fin d => (e i, true))) ∈ F₀)
    (t : ℕ) (ht : t < d - 1) :
    ∀ π₀, IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' F₀) π₀ →
      ∃ π', IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' F₀) π' ∧
        (∀ L ∈ π₀, L ∈ π') ∧
        (insert ({(prefSet e t, true)} : LinTerm U)
          ((Finset.univ.filter (fun i : Fin d => t < i.val)).image (fun i => ({({e i}, true)} : LinTerm U)))) ∈ π' ∧
        π'.length ≤ π₀.length + (4 * d + 5) * (t + 1) := by
  induction t with
  | zero =>
    intro π₀ hder
    let Cl := Finset.univ.image (fun i : Fin d => (e i, true))
    have hline : linKOfClause Cl =
        insert ({(prefSet e 0, true)} : LinTerm U)
          ((Finset.univ.filter (fun i : Fin d => 0 < i.val)).image (fun i => ({({e i}, true)} : LinTerm U))) := by
      have h0lt : 0 < d := by omega
      rw [prefSet_zero h0lt e]
      ext S
      simp only [Cl, linKOfClause, linOfClause, Finset.mem_insert, Finset.mem_image,
        Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, rfl⟩
        by_cases hi0 : i.val = 0
        · have hi_eq : i = ⟨0, h0lt⟩ := Fin.ext hi0
          subst hi_eq
          left; rfl
        · right; exact ⟨i, by omega, rfl⟩
      · rintro (rfl | ⟨i, _, rfl⟩)
        · exact ⟨({e ⟨0, h0lt⟩}, true), ⟨(e ⟨0, h0lt⟩, true), ⟨⟨0, h0lt⟩, rfl⟩, rfl⟩, rfl⟩
        · exact ⟨({e i}, true), ⟨(e i, true), ⟨i, rfl⟩, rfl⟩, rfl⟩
    have hd1 := IsLinKDerivation.ax hder ⟨Cl, halo, rfl⟩ (fun T hT => by
      rw [linKOfClause_card_one Cl T hT]; exact hk)
    dsimp only at hd1
    rw [hline] at hd1
    refine ⟨_ :: π₀, hd1, fun L hL => by simp [hL], by simp, ?_⟩
    simp only [List.length_cons]
    omega
  | succ t ih =>
    intro π₀ hder
    rcases ih (by omega) π₀ hder with ⟨π₁, hder1, hsub1, hLt, hlen1⟩
    have ht1d : t + 1 < d := by omega
    let j1 : Fin d := ⟨t + 1, ht1d⟩
    rcases derive_amo_prefix hk F₀ hinj hamo j1 t (by dsimp [j1]; omega) π₁ hder1 with
      ⟨π₂, hder2, hsub2, hBt, hlen2⟩
    let tailSet : LinKLine U :=
      (Finset.univ.filter (fun i : Fin d => t + 1 < i.val)).image (fun i => ({({e i}, true)} : LinTerm U))
    let M₁ : LinKLine U :=
      insert ({(prefSet e (t + 1), true)} : LinTerm U)
        (insert ({({e j1}, true)} : LinTerm U) tailSet)
    have hM₁1 : ∀ S ∈ M₁, S.card = 1 := by
      intro S hS
      simp only [M₁, tailSet, Finset.mem_insert, Finset.mem_image] at hS
      rcases hS with rfl | rfl | ⟨_, _, rfl⟩ <;> simp
    have hweak1 : IsLinKWeakening
        (insert ({(prefSet e t, true)} : LinTerm U)
          ((Finset.univ.filter (fun i : Fin d => t < i.val)).image (fun i => ({({e i}, true)} : LinTerm U)))) M₁ := by
      apply isLinKWeakening_one_sem hM₁1
      intro a hsat
      rcases hsat with ⟨T, hT, hTsat⟩
      simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hT
      rcases hT with rfl | ⟨i, hit, rfl⟩
      · have hp : parity a (prefSet e t) = true := by
          have := hTsat _ (Finset.mem_singleton_self _)
          rwa [linEqSat_iff_parity] at this
        cases he : a (e j1)
        · refine ⟨{(prefSet e (t + 1), true)}, by simp [M₁], fun q hq => ?_⟩
          rw [Finset.mem_singleton.mp hq, linEqSat_iff_parity,
            prefSet_succ e t ht1d, parity_insert a _ _ (not_mem_prefSet hinj t ht1d), he, hp]
          rfl
        · refine ⟨{({e j1}, true)}, by simp [M₁], fun q hq => ?_⟩
          rw [Finset.mem_singleton.mp hq, linEqSat_iff_parity, parity_singleton, he]
      · by_cases hi1 : i.val = t + 1
        · have hij : i = j1 := Fin.ext hi1
          refine ⟨{({e j1}, true)}, by simp [M₁], by simpa [hij] using hTsat⟩
        · refine ⟨{({e i}, true)}, ?_, hTsat⟩
          simp only [M₁, tailSet, Finset.mem_insert, Finset.mem_image, Finset.mem_filter,
            Finset.mem_univ, true_and]
          right; right; exact ⟨i, by omega, rfl⟩
    have hder3 := IsLinKDerivation.weak hder2 (hsub2 _ hLt) hweak1
      (fun T hT => by rw [hM₁1 T hT]; exact hk)
    let M₂ : LinKLine U := {{({e j1}, false)}, {(prefSet e (t + 1), true)}}
    have hM₂1 : ∀ S ∈ M₂, S.card = 1 := by
      intro S hS; simp only [M₂, Finset.mem_insert, Finset.mem_singleton] at hS
      rcases hS with rfl | rfl <;> simp
    have hweak2 : IsLinKWeakening {{(prefSet e t, false)}, {({e j1}, false)}} M₂ := by
      apply isLinKWeakening_one_sem hM₂1
      intro a hsat
      rcases hsat with ⟨T, hT, hTsat⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hT
      rcases hT with rfl | rfl
      · have hp : parity a (prefSet e t) = false := by
          have := hTsat _ (Finset.mem_singleton_self _)
          rwa [linEqSat_iff_parity] at this
        cases he : a (e j1)
        · refine ⟨{({e j1}, false)}, by simp [M₂], fun q hq => ?_⟩
          rw [Finset.mem_singleton.mp hq, linEqSat_iff_parity, parity_singleton, he]
        · refine ⟨{(prefSet e (t + 1), true)}, by simp [M₂], fun q hq => ?_⟩
          rw [Finset.mem_singleton.mp hq, linEqSat_iff_parity,
            prefSet_succ e t ht1d, parity_insert a _ _ (not_mem_prefSet hinj t ht1d), he, hp]
          rfl
      · exact ⟨{({e j1}, false)}, by simp [M₂], hTsat⟩
    have hder4 := IsLinKDerivation.weak hder3 (by simp [hBt]) hweak2
      (fun T hT => by rw [hM₂1 T hT]; exact hk)
    let R : LinKLine U := insert ({(prefSet e (t + 1), true)} : LinTerm U) tailSet
    have hR1 : ∀ S ∈ R, S.card = 1 := by
      intro S hS; simp only [R, tailSet, Finset.mem_insert, Finset.mem_image] at hS
      rcases hS with rfl | ⟨_, _, rfl⟩ <;> simp
    have hRsub : M₁.erase {({e j1}, true)} ∪ M₂.erase {negLinEq ({e j1}, true)} ⊆ R := by
      intro S hS
      simp only [M₁, M₂, R, negLinEq, Bool.not_true, Finset.mem_union, Finset.mem_erase,
        Finset.mem_insert, Finset.mem_singleton] at hS ⊢
      rcases hS with ⟨hne1, rfl | rfl | htail⟩ | ⟨hne2, rfl | rfl⟩
      · left; rfl
      · exact absurd rfl hne1
      · right; exact htail
      · exact absurd rfl hne2
      · left; rfl
    rcases derive_cut_one hk hder4 (by simp) (by simp) ({e j1}, true)
      (by simp [M₁]) (by simp [M₂, negLinEq]) hR1 hRsub with ⟨π₅, hder5, hsub5, hRin5, hlen5⟩
    refine ⟨π₅, hder5, fun L hL => hsub5 _ (by simp [hsub2 _ (hsub1 L hL)]), hRin5, ?_⟩
    simp only [List.length_cons] at hlen5
    have hbound : 4 * (t + 1) ≤ 4 * d := by omega
    have hmul : (4 * d + 5) * (t + 1 + 1) = (4 * d + 5) * (t + 1) + (4 * d + 5) := by ring
    omega

end AffineSim

section GenBipDefs

abbrev GenBip (L R : Type) : Type := L → Finset R

def gRightNbrs {L R : Type} [Fintype L] [DecidableEq R] (G : GenBip L R) (v : R) : Finset L :=
  Finset.univ.filter (fun u => v ∈ G u)

lemma mem_gRightNbrs_iff {L R : Type} [Fintype L] [DecidableEq R] (G : GenBip L R) (v : R) (u : L) :
    u ∈ gRightNbrs G v ↔ v ∈ G u := by
  simp [gRightNbrs]

abbrev GenEdge {L R : Type} (G : GenBip L R) : Type := {e : L × R // e.2 ∈ G e.1}

def genGraphPHP {L R : Type} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (G : GenBip L R) : Set (Clause (GenEdge G)) :=
  {C | ∃ i : L, C = Finset.univ.filter (fun l : Literal (GenEdge G) => l.1.1.1 = i ∧ l.2 = true)} ∪
  {C | ∃ (e e' : GenEdge G), e.1.2 = e'.1.2 ∧ e.1.1 ≠ e'.1.1 ∧ C = {(e, false), (e', false)}} ∪
  {C | ∃ (e e' : GenEdge G), e.1.1 = e'.1.1 ∧ e.1.2 ≠ e'.1.2 ∧ C = {(e, false), (e', false)}}

def GenConn {L R : Type} (G : GenBip L R) : Prop :=
  ∀ f : L ⊕ R → Bool, (∀ u, ∀ v ∈ G u, f (Sum.inl u) = f (Sum.inr v)) → ∀ x y, f x = f y

lemma card_genEdge_eq_sum_left {L R : Type} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (G : GenBip L R) :
    Fintype.card (GenEdge G) = ∑ u : L, (G u).card := by
  let e : GenEdge G ≃ Σ u : L, {v : R // v ∈ G u} := {
    toFun := fun x => ⟨x.1.1, ⟨x.1.2, x.2⟩⟩,
    invFun := fun y => ⟨(y.1, y.2.1), y.2.2⟩,
    left_inv := fun _ => rfl,
    right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  refine Finset.sum_congr rfl (fun u _ => Fintype.card_coe (G u))

lemma card_genEdge_eq_sum_right {L R : Type} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (G : GenBip L R) :
    Fintype.card (GenEdge G) = ∑ v : R, (gRightNbrs G v).card := by
  let e : GenEdge G ≃ Σ v : R, {u : L // u ∈ gRightNbrs G v} := {
    toFun := fun x => ⟨x.1.2, ⟨x.1.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩⟩⟩,
    invFun := fun y => ⟨(y.2.1, y.1), (Finset.mem_filter.mp y.2.2).2⟩,
    left_inv := fun _ => rfl,
    right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  refine Finset.sum_congr rfl (fun v _ => Fintype.card_coe (gRightNbrs G v))

lemma relabel_genBip {L R : Type} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
    (G : GenBip L R) (q : ℕ) (hL : Fintype.card L = q + 1) (hR : Fintype.card R = q)
    (hdegL : ∀ u : L, 2 ≤ (G u).card ∧ (G u).card ≤ 3)
    (hdegR : ∀ v : R, 2 ≤ (gRightNbrs G v).card ∧ (gRightNbrs G v).card ≤ 3)
    (hconn : GenConn G)
    (P : ℕ → Prop)
    (hgirthP : ∀ (a : ℕ) (us : Fin (a + 2) ↪ L) (vs : Fin (a + 2) ↪ R),
      (∀ i, vs i ∈ G (us i) ∧ vs i ∈ G (us (i + 1))) → P (2 * (a + 2))) :
    ∃ G' : BipGraph (q + 1) q,
      Fintype.card (GEdge G') = Fintype.card (GenEdge G) ∧
      (∀ u, 2 ≤ (G' u).card ∧ (G' u).card ≤ 3) ∧
      (∀ v, 2 ≤ (rightNbrs G' v).card ∧ (rightNbrs G' v).card ≤ 3) ∧
      (∀ f : Fin (q + 1) ⊕ Fin q → Bool,
        (∀ u, ∀ v ∈ G' u, f (Sum.inl u) = f (Sum.inr v)) → ∀ x y, f x = f y) ∧
      (∀ (a : ℕ) (us : Fin (a + 2) ↪ Fin (q + 1)) (vs : Fin (a + 2) ↪ Fin q),
        (∀ i, vs i ∈ G' (us i) ∧ vs i ∈ G' (us (i + 1))) → P (2 * (a + 2))) ∧
      (∀ (k : ℕ) (π : List (LinKLine (GEdge G'))), 1 ≤ k →
        IsLinKRefutation k (funGraphPHP G') π →
        ∃ π₀ : List (LinKLine (GenEdge G)),
          IsLinKRefutation k (genGraphPHP G) π₀ ∧ π₀.length ≤ 1 + 2 * π.length) := by
  let eL : L ≃ Fin (q + 1) := Fintype.equivFinOfCardEq hL
  let eR : R ≃ Fin q := Fintype.equivFinOfCardEq hR
  let G' : BipGraph (q + 1) q := fun u => (G (eL.symm u)).image eR
  have hmem' : ∀ u v, v ∈ G' u ↔ eR.symm v ∈ G (eL.symm u) := by
    intro u v
    simp only [G', Finset.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩; simpa using hw
    · intro hw; exact ⟨eR.symm v, hw, by simp⟩
  let eE : GEdge G' ≃ GenEdge G := {
    toFun := fun x => ⟨(eL.symm x.1.1, eR.symm x.1.2), (hmem' x.1.1 x.1.2).mp x.2⟩,
    invFun := fun y => ⟨(eL y.1.1, eR y.1.2), (hmem' _ _).mpr (by simpa using y.2)⟩,
    left_inv := fun x => Subtype.ext (Prod.ext (by simp) (by simp)),
    right_inv := fun y => Subtype.ext (Prod.ext (by simp) (by simp)) }
  refine ⟨G', Fintype.card_congr eE, ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    have hc : (G' u).card = (G (eL.symm u)).card := Finset.card_image_of_injective _ eR.injective
    rw [hc]; exact hdegL (eL.symm u)
  · intro v
    have hset : rightNbrs G' v = (gRightNbrs G (eR.symm v)).image eL := by
      ext u
      simp only [rightNbrs, gRightNbrs, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_image, hmem']
      constructor
      · intro h; exact ⟨eL.symm u, h, by simp⟩
      · rintro ⟨w, hw, rfl⟩; simpa using hw
    rw [hset, Finset.card_image_of_injective _ eL.injective]
    exact hdegR (eR.symm v)
  · intro f hf x y
    let f₀ : L ⊕ R → Bool := fun z => match z with
      | Sum.inl u => f (Sum.inl (eL u))
      | Sum.inr v => f (Sum.inr (eR v))
    have hf₀ : ∀ u, ∀ v ∈ G u, f₀ (Sum.inl u) = f₀ (Sum.inr v) := by
      intro u v hv
      exact hf (eL u) (eR v) ((hmem' _ _).mpr (by simpa using hv))
    have hconst := hconn f₀ hf₀
    rcases x with u1 | v1 <;> rcases y with u2 | v2
    · simpa [f₀] using hconst (Sum.inl (eL.symm u1)) (Sum.inl (eL.symm u2))
    · simpa [f₀] using hconst (Sum.inl (eL.symm u1)) (Sum.inr (eR.symm v2))
    · simpa [f₀] using hconst (Sum.inr (eR.symm v1)) (Sum.inl (eL.symm u2))
    · simpa [f₀] using hconst (Sum.inr (eR.symm v1)) (Sum.inr (eR.symm v2))
  · intro a us vs hcyc
    refine hgirthP a (us.trans eL.symm.toEmbedding) (vs.trans eR.symm.toEmbedding) (fun i => ?_)
    have h1 := (hmem' (us i) (vs i)).mp (hcyc i).1
    have h2 := (hmem' (us (i + 1)) (vs i)).mp (hcyc i).2
    exact ⟨h1, h2⟩
  · intro k π hk hπ
    let σ : GEdge G' → LinEq (GenEdge G) := fun e => ({eE e}, false)
    let u0 : L := eL.symm ⟨0, Nat.succ_pos q⟩
    let A₀ : Clause (GenEdge G) :=
      Finset.univ.filter (fun l : Literal (GenEdge G) => l.1.1.1 = u0 ∧ l.2 = true)
    have hA₀ : A₀ ∈ genGraphPHP G := Or.inl (Or.inl ⟨u0, rfl⟩)
    have hax : ∀ C ∈ funGraphPHP G', ∀ π₀,
        IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' genGraphPHP G) π₀ →
        linKOfClause A₀ ∈ π₀ →
        ∃ π', IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' genGraphPHP G) π' ∧
          (∀ L ∈ π₀, L ∈ π') ∧ substLine σ (linKOfClause C) ∈ π' ∧ π'.length ≤ π₀.length + 1 := by
      intro C hC π₀ hder _
      have hC' : ∃ C₀ ∈ genGraphPHP G, substLine σ (linKOfClause C) = linKOfClause C₀ := by
        have hsubst_eq : ∀ D : Clause (GEdge G'),
            substLine σ (linKOfClause D) = linKOfClause (D.image (fun l => (eE l.1, l.2))) := by
          intro D
          rw [substLine_of_clause]
          ext S
          simp only [σ, Bool.xor_false, linKOfClause, linOfClause, Finset.mem_image]
          constructor
          · rintro ⟨l, hlD, rfl⟩
            exact ⟨({eE l.1}, l.2), ⟨(eE l.1, l.2), ⟨l, hlD, rfl⟩, rfl⟩, rfl⟩
          · rintro ⟨_, ⟨_, ⟨l, hlD, rfl⟩, rfl⟩, rfl⟩
            exact ⟨l, hlD, rfl⟩
        rw [hsubst_eq]
        rcases hC with (⟨u, rfl⟩ | ⟨e1, e2, he2, hne1, rfl⟩) | ⟨e1, e2, he1, hne2, rfl⟩
        · refine ⟨Finset.univ.filter (fun l : Literal (GenEdge G) => l.1.1.1 = eL.symm u ∧ l.2 = true),
            Or.inl (Or.inl ⟨eL.symm u, rfl⟩), ?_⟩
          congr 1
          ext ⟨e, b⟩
          simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
          constructor
          · rintro ⟨⟨e', b'⟩, ⟨he'u, hb'⟩, rfl, rfl⟩
            exact ⟨by dsimp [eE]; rw [he'u], hb'⟩
          · rintro ⟨heu, hb⟩
            refine ⟨(eE.symm e, b), ⟨?_, hb⟩, by simp⟩
            have : eL.symm (eE.symm e).1.1 = eL.symm u := by
              have h1 : eL.symm (eE.symm e).1.1 = e.1.1 :=
                congrArg (fun x : GenEdge G => x.1.1) (eE.apply_symm_apply e)
              rw [h1, heu]
            exact eL.symm.injective this
        · refine ⟨{(eE e1, false), (eE e2, false)}, Or.inl (Or.inr ⟨eE e1, eE e2, ?_, ?_, rfl⟩), by simp⟩
          · simp [eE, he2]
          · intro h; exact hne1 (eL.symm.injective h)
        · refine ⟨{(eE e1, false), (eE e2, false)}, Or.inr ⟨eE e1, eE e2, ?_, ?_, rfl⟩, by simp⟩
          · simp [eE, he1]
          · intro h; exact hne2 (eR.symm.injective h)
      rcases hC' with ⟨C₀, hC₀, heq⟩
      rw [heq]
      have hd1 := IsLinKDerivation.ax hder ⟨C₀, hC₀, rfl⟩
        (fun T hT => by rw [linKOfClause_card_one C₀ T hT]; exact hk)
      exact ⟨_ :: π₀, hd1, fun L hL => by simp [hL], by simp, by simp⟩
    have hsim := affine_sim k 1 hk (genGraphPHP G) (funGraphPHP G') A₀ hA₀ σ hax π hπ
    simpa using hsim

end GenBipDefs

section CycleExtraction

lemma fin_add_one_ne_self {M : ℕ} [NeZero M] (hM : 2 ≤ M) (r : Fin M) : r + 1 ≠ r := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_add, Fin.val_one'] at hv
  rw [Nat.mod_eq_of_lt (by omega : 1 < M)] at hv
  have hrlt : r.val < M := r.isLt
  by_cases hlt : r.val + 1 < M
  · rw [Nat.mod_eq_of_lt hlt] at hv; omega
  · rw [show r.val + 1 = M by omega, Nat.mod_self] at hv; omega

lemma fin_add_two_ne_self {M : ℕ} [NeZero M] (hM : 3 ≤ M) (r : Fin M) : r + 1 + 1 ≠ r := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_add, Fin.val_one'] at hv
  rw [Nat.mod_eq_of_lt (by omega : 1 < M)] at hv
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod] at hv
  have hrlt : r.val < M := r.isLt
  by_cases hlt : r.val + 1 + 1 < M
  · rw [Nat.mod_eq_of_lt hlt] at hv; omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hv; omega

lemma fin_sub_one_ne_add_one {M : ℕ} [NeZero M] (hM : 3 ≤ M) (r : Fin M) : r - 1 ≠ r + 1 := by
  intro h
  have h1 : (r - 1) + 1 = (r + 1) + 1 := congrArg (· + 1) h
  have hsub : (r - 1) + 1 = r := sub_add_cancel r 1
  rw [hsub] at h1
  exact fin_add_two_ne_self hM r h1.symm

lemma closed_trail_has_cycle {m n : ℕ} (G : BipGraph m n) :
    ∀ r : ℕ,
      ∀ (u : Fin (r + 1) → Fin m) (v : Fin (r + 1) → Fin n),
        (∀ i : Fin (r + 1), v i ∈ G (u i) ∧ v i ∈ G (u (i + 1))) →
        (∀ i j : Fin (r + 1), i ≠ j → ¬ (u i = u j ∧ v i = v j)) →
        (∀ i j : Fin (r + 1), i ≠ j → ¬ (u (i + 1) = u (j + 1) ∧ v i = v j)) →
        (∀ i j : Fin (r + 1), ¬ (u i = u (j + 1) ∧ v i = v j)) →
        ∃ (a : ℕ) (us : Fin (a + 2) ↪ Fin m) (vs : Fin (a + 2) ↪ Fin n),
          a + 2 ≤ r + 1 ∧ ∀ i, vs i ∈ G (us i) ∧ vs i ∈ G (us (i + 1)) := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro u v hadj hne1 hne2 hne3
    have hr1 : 1 ≤ r := by
      by_contra hlt
      have hr : r = 0 := by omega
      subst hr
      exact hne3 0 0 ⟨by simp, rfl⟩
    by_cases huinj : Function.Injective u
    · by_cases hvinj : Function.Injective v
      · refine ⟨r - 1, ⟨fun i => u ⟨i.val, by omega⟩, ?_⟩, ⟨fun i => v ⟨i.val, by omega⟩, ?_⟩,
          by omega, ?_⟩
        · intro i j hij
          have h := congrArg Fin.val (huinj hij)
          exact Fin.ext h
        · intro i j hij
          have h := congrArg Fin.val (hvinj hij)
          exact Fin.ext h
        · intro i
          have h1 := hadj ⟨i.val, by omega⟩
          have hsucc : (⟨(i + 1).val, by have := (i + 1).isLt; omega⟩ : Fin (r + 1)) = ⟨i.val, by omega⟩ + 1 := by
            apply Fin.ext
            simp only [Fin.val_add, Fin.val_one']
            have hrr : r - 1 + 2 = r + 1 := by omega
            simp only [hrr]
          change v ⟨i.val, _⟩ ∈ G (u ⟨i.val, _⟩) ∧ v ⟨i.val, _⟩ ∈ G (u ⟨(i + 1).val, _⟩)
          rw [hsucc]
          exact h1
      · unfold Function.Injective at hvinj
        push Not at hvinj
        rcases hvinj with ⟨i0, j0, hvij, hneij⟩
        wlog hlt : i0.val < j0.val generalizing i0 j0
        · exact this j0 i0 hvij.symm hneij.symm (by omega)
        let r' := j0.val - i0.val - 1
        have hr'eq : r' + 1 = j0.val - i0.val := by omega
        have hr'lt : r' < r := by omega
        let u' : Fin (r' + 1) → Fin m := fun t => u ⟨(i0.val + 1 + t.val) % (r + 1), Nat.mod_lt _ (by omega)⟩
        let v' : Fin (r' + 1) → Fin n := fun t => v ⟨(i0.val + 1 + t.val) % (r + 1), Nat.mod_lt _ (by omega)⟩
        have hidx_eq : ∀ t : Fin (r' + 1), (⟨(i0.val + 1 + t.val) % (r + 1), Nat.mod_lt _ (by omega)⟩ : Fin (r + 1)) =
            ⟨i0.val + 1 + t.val, by omega⟩ := by
          intro t; apply Fin.ext; exact Nat.mod_eq_of_lt (by omega)
        have hstep : ∀ t : Fin (r' + 1), (⟨(i0.val + 1 + t.val) % (r + 1), Nat.mod_lt _ (by omega)⟩ : Fin (r + 1)) + 1 =
            if t.val + 1 < r' + 1 then ⟨(i0.val + 1 + (t + 1).val) % (r + 1), Nat.mod_lt _ (by omega)⟩
            else j0 + 1 := by
          intro t
          split_ifs with ht
          · apply Fin.ext
            have h1 : (t + 1).val = t.val + 1 := by
              simp only [Fin.val_add, Fin.val_one']
              rw [Nat.mod_eq_of_lt (by omega : 1 < r' + 1), Nat.mod_eq_of_lt ht]
            simp only [Fin.val_add, Fin.val_one', h1]
            rw [Nat.mod_eq_of_lt (by omega : 1 < r + 1),
                Nat.mod_eq_of_lt (by omega : i0.val + 1 + t.val < r + 1),
                Nat.mod_eq_of_lt (by omega : i0.val + 1 + t.val + 1 < r + 1),
                Nat.mod_eq_of_lt (by omega : i0.val + 1 + (t.val + 1) < r + 1)]
            omega
          · apply Fin.ext
            have htlast : t.val + 1 = r' + 1 := by omega
            simp only [Fin.val_add, Fin.val_one']
            rw [Nat.mod_eq_of_lt (by omega : 1 < r + 1),
                Nat.mod_eq_of_lt (by omega : i0.val + 1 + t.val < r + 1)]
            have : i0.val + 1 + t.val + 1 = j0.val + 1 := by omega
            rw [this]
        have hlast_v : ∀ t : Fin (r' + 1), t.val + 1 = r' + 1 → v' t = v i0 := by
          intro t ht
          have heq : (⟨(i0.val + 1 + t.val) % (r + 1), Nat.mod_lt _ (by omega)⟩ : Fin (r + 1)) = j0 := by
            apply Fin.ext; dsimp only; rw [Nat.mod_eq_of_lt (by omega)]; omega
          simp only [v', heq, hvij.symm]
        have hidx_inj : Function.Injective (fun t : Fin (r' + 1) => (⟨(i0.val + 1 + t.val) % (r + 1), Nat.mod_lt _ (by omega)⟩ : Fin (r + 1))) := by
          intro a b hab
          dsimp only at hab
          rw [hidx_eq a, hidx_eq b] at hab
          have := congrArg Fin.val hab; dsimp at this; exact Fin.ext (by omega)
        have hu'0 : u' 0 = u (i0 + 1) := by
          simp only [u', Fin.val_zero, add_zero]
          congr 1; apply Fin.ext; simp only [Fin.val_add, Fin.val_one']
          rw [Nat.mod_eq_of_lt (by omega : 1 < r + 1)]
        have ht_last0 : ∀ t : Fin (r' + 1), t.val + 1 = r' + 1 → t + 1 = 0 := by
          intro t htlast
          apply Fin.ext; simp only [Fin.val_add, Fin.val_one', Fin.val_zero]
          by_cases hr'2 : 1 < r' + 1
          · rw [Nat.mod_eq_of_lt hr'2, htlast, Nat.mod_self]
          · have hr0 : r' = 0 := by omega
            have ht0 : t.val = 0 := by omega
            simp [hr0, ht0]
        have hadj' : ∀ t : Fin (r' + 1), v' t ∈ G (u' t) ∧ v' t ∈ G (u' (t + 1)) := by
          intro t
          refine ⟨(hadj _).1, ?_⟩
          by_cases ht : t.val + 1 < r' + 1
          · have h2 := (hadj ⟨(i0.val + 1 + t.val) % (r + 1), Nat.mod_lt _ (by omega)⟩).2
            rw [hstep t] at h2; simp only [ht, ↓reduceIte] at h2
            exact h2
          · have htlast : t.val + 1 = r' + 1 := by omega
            rw [ht_last0 t htlast, hu'0, hlast_v t htlast]
            exact (hadj i0).2
        have hne1' : ∀ a b : Fin (r' + 1), a ≠ b → ¬ (u' a = u' b ∧ v' a = v' b) := fun a b hab =>
          hne1 _ _ (fun h => hab (hidx_inj h))
        have hne2' : ∀ a b : Fin (r' + 1), a ≠ b → ¬ (u' (a + 1) = u' (b + 1) ∧ v' a = v' b) := by
          intro a b hab ⟨huab, hvab⟩
          by_cases ha : a.val + 1 < r' + 1 <;> by_cases hb : b.val + 1 < r' + 1
          · have h1 := hstep a; simp only [ha, ↓reduceIte] at h1
            have h2 := hstep b; simp only [hb, ↓reduceIte] at h2
            exact hne2 _ _ (fun h => hab (hidx_inj h)) ⟨by simpa [u', h1, h2] using huab, hvab⟩
          · have hblast : b.val + 1 = r' + 1 := by omega
            rw [ht_last0 b hblast, hu'0] at huab
            rw [hlast_v b hblast] at hvab
            have h1 := hstep a; simp only [ha, ↓reduceIte] at h1
            have hne_ai : (⟨(i0.val + 1 + a.val) % (r + 1), Nat.mod_lt _ (by omega)⟩ : Fin (r + 1)) ≠ i0 := by
              rw [hidx_eq a]; intro h; have := congrArg Fin.val h; dsimp at this; omega
            exact hne2 _ i0 hne_ai ⟨by simpa [u', h1] using huab, hvab⟩
          · have halast : a.val + 1 = r' + 1 := by omega
            rw [ht_last0 a halast, hu'0] at huab
            rw [hlast_v a halast] at hvab
            have h2 := hstep b; simp only [hb, ↓reduceIte] at h2
            have hne_bi : i0 ≠ (⟨(i0.val + 1 + b.val) % (r + 1), Nat.mod_lt _ (by omega)⟩ : Fin (r + 1)) := by
              rw [hidx_eq b]; intro h; have := congrArg Fin.val h; dsimp at this; omega
            exact hne2 i0 _ hne_bi ⟨by simpa [u', h2] using huab, hvab⟩
          · exact hab (Fin.ext (by omega))
        have hne3' : ∀ a b : Fin (r' + 1), ¬ (u' a = u' (b + 1) ∧ v' a = v' b) := by
          intro a b ⟨huab, hvab⟩
          by_cases hb : b.val + 1 < r' + 1
          · have h2 := hstep b; simp only [hb, ↓reduceIte] at h2
            exact hne3 _ _ ⟨by simpa [u', h2] using huab, hvab⟩
          · have hblast : b.val + 1 = r' + 1 := by omega
            rw [ht_last0 b hblast, hu'0] at huab
            rw [hlast_v b hblast] at hvab
            exact hne3 _ i0 ⟨huab, hvab⟩
        rcases ih r' hr'lt u' v' hadj' hne1' hne2' hne3' with ⟨a, us, vs, hale, hcyc⟩
        exact ⟨a, us, vs, le_trans hale (by omega), hcyc⟩
    · unfold Function.Injective at huinj
      push Not at huinj
      rcases huinj with ⟨i0, j0, huij, hneij⟩
      wlog hlt : i0.val < j0.val generalizing i0 j0
      · exact this j0 i0 huij.symm hneij.symm (by omega)
      let r' := j0.val - i0.val - 1
      have hr'eq : r' + 1 = j0.val - i0.val := by omega
      have hr'lt : r' < r := by omega
      let u' : Fin (r' + 1) → Fin m := fun t => u ⟨i0.val + t.val, by omega⟩
      let v' : Fin (r' + 1) → Fin n := fun t => v ⟨i0.val + t.val, by omega⟩
      have hidx_inj : Function.Injective (fun t : Fin (r' + 1) => (⟨i0.val + t.val, by omega⟩ : Fin (r + 1))) := by
        intro a b hab
        have := congrArg Fin.val hab; dsimp at this; exact Fin.ext (by omega)
      have hstep : ∀ t : Fin (r' + 1), (⟨i0.val + t.val, by omega⟩ : Fin (r + 1)) + 1 =
          if t.val + 1 < r' + 1 then ⟨i0.val + (t + 1).val, by have := (t + 1).isLt; omega⟩ else j0 := by
        intro t
        split_ifs with ht
        · apply Fin.ext
          have h1 : (t + 1).val = t.val + 1 := by
            simp only [Fin.val_add, Fin.val_one']
            rw [Nat.mod_eq_of_lt (by omega : 1 < r' + 1), Nat.mod_eq_of_lt ht]
          simp only [Fin.val_add, Fin.val_one', h1]
          rw [Nat.mod_eq_of_lt (by omega : 1 < r + 1), Nat.mod_eq_of_lt (by omega : i0.val + t.val + 1 < r + 1)]
          omega
        · apply Fin.ext
          simp only [Fin.val_add, Fin.val_one']
          rw [Nat.mod_eq_of_lt (by omega : 1 < r + 1), Nat.mod_eq_of_lt (by omega : i0.val + t.val + 1 < r + 1)]
          omega
      have hu'0 : u' 0 = u j0 := by
        simp only [u', Fin.val_zero, add_zero]; exact huij
      have ht_last0 : ∀ t : Fin (r' + 1), t.val + 1 = r' + 1 → t + 1 = 0 := by
        intro t htlast
        apply Fin.ext; simp only [Fin.val_add, Fin.val_one', Fin.val_zero]
        by_cases hr'2 : 1 < r' + 1
        · rw [Nat.mod_eq_of_lt hr'2, htlast, Nat.mod_self]
        · have hr0 : r' = 0 := by omega
          have ht0 : t.val = 0 := by omega
          simp [hr0, ht0]
      have hadj' : ∀ t : Fin (r' + 1), v' t ∈ G (u' t) ∧ v' t ∈ G (u' (t + 1)) := by
        intro t
        refine ⟨(hadj _).1, ?_⟩
        have h2 := (hadj ⟨i0.val + t.val, by omega⟩).2
        by_cases ht : t.val + 1 < r' + 1
        · rw [hstep t] at h2; simp only [ht, ↓reduceIte] at h2; exact h2
        · have htlast : t.val + 1 = r' + 1 := by omega
          rw [ht_last0 t htlast, hu'0]
          rw [hstep t] at h2; simp only [ht, ↓reduceIte] at h2; exact h2
      have hne1' : ∀ a b : Fin (r' + 1), a ≠ b → ¬ (u' a = u' b ∧ v' a = v' b) := fun a b hab =>
        hne1 _ _ (fun h => hab (hidx_inj h))
      have hne2' : ∀ a b : Fin (r' + 1), a ≠ b → ¬ (u' (a + 1) = u' (b + 1) ∧ v' a = v' b) := by
        intro a b hab ⟨huab, hvab⟩
        have hu_eq : ∀ t : Fin (r' + 1), u' (t + 1) = u ((⟨i0.val + t.val, by omega⟩ : Fin (r + 1)) + 1) := by
          intro t
          by_cases ht : t.val + 1 < r' + 1
          · rw [hstep t]; simp only [ht, ↓reduceIte]; rfl
          · have htlast : t.val + 1 = r' + 1 := by omega
            rw [ht_last0 t htlast, hu'0, hstep t]; simp only [ht, ↓reduceIte]
        rw [hu_eq a, hu_eq b] at huab
        exact hne2 _ _ (fun h => hab (hidx_inj h)) ⟨huab, hvab⟩
      have hne3' : ∀ a b : Fin (r' + 1), ¬ (u' a = u' (b + 1) ∧ v' a = v' b) := by
        intro a b ⟨huab, hvab⟩
        have hu_eq : u' (b + 1) = u ((⟨i0.val + b.val, by omega⟩ : Fin (r + 1)) + 1) := by
          by_cases ht : b.val + 1 < r' + 1
          · rw [hstep b]; simp only [ht, ↓reduceIte]; rfl
          · have htlast : b.val + 1 = r' + 1 := by omega
            rw [ht_last0 b htlast, hu'0, hstep b]; simp only [ht, ↓reduceIte]
        rw [hu_eq] at huab
        exact hne3 _ _ ⟨huab, hvab⟩
      rcases ih r' hr'lt u' v' hadj' hne1' hne2' hne3' with ⟨a, us, vs, hale, hcyc⟩
      exact ⟨a, us, vs, le_trans hale (by omega), hcyc⟩

end CycleExtraction

section Subcubicize

variable {q₀ : ℕ} (G₀ : BipGraph (q₀ + 1) q₀)

def degL (u : Fin (q₀ + 1)) : ℕ := (G₀ u).card
def degR (v : Fin q₀) : ℕ := (rightNbrs G₀ v).card

noncomputable def enumL (u : Fin (q₀ + 1)) : Fin (degL G₀ u) ≃ {v // v ∈ G₀ u} :=
  (G₀ u).equivFin.symm

noncomputable def enumR (v : Fin q₀) : Fin (degR G₀ v) ≃ {u // u ∈ rightNbrs G₀ v} :=
  (rightNbrs G₀ v).equivFin.symm

abbrev L1 (G₀ : BipGraph (q₀ + 1) q₀) : Type :=
  (Σ u : Fin (q₀ + 1), Fin (degL G₀ u)) ⊕ (Σ v : Fin q₀, Fin (degR G₀ v - 1))

abbrev R1 (G₀ : BipGraph (q₀ + 1) q₀) : Type :=
  (Σ v : Fin q₀, Fin (degR G₀ v)) ⊕ (Σ u : Fin (q₀ + 1), Fin (degL G₀ u - 1))

noncomputable def portEdgeL (u : Fin (q₀ + 1)) (j : Fin (degL G₀ u)) : GEdge G₀ :=
  ⟨(u, (enumL G₀ u j).1), (enumL G₀ u j).2⟩

noncomputable def portEdgeR (v : Fin q₀) (j : Fin (degR G₀ v)) : GEdge G₀ :=
  ⟨((enumR G₀ v j).1, v), (Finset.mem_filter.mp (enumR G₀ v j).2).2⟩

noncomputable def adj1Prop (x : L1 G₀) (y : R1 G₀) : Prop :=
  match x, y with
  | Sum.inl ⟨u, j⟩, Sum.inl ⟨v, j'⟩ => (enumL G₀ u j).1 = v ∧ (enumR G₀ v j').1 = u
  | Sum.inl ⟨u, j⟩, Sum.inr ⟨u', t⟩ => u = u' ∧ (j.val = t.val ∨ j.val = t.val + 1)
  | Sum.inr ⟨v', t⟩, Sum.inl ⟨v, j⟩ => v = v' ∧ (j.val = t.val ∨ j.val = t.val + 1)
  | Sum.inr _, Sum.inr _ => False

noncomputable def G1 : GenBip (L1 G₀) (R1 G₀) := by
  classical
  exact fun x => Finset.univ.filter (fun y => adj1Prop G₀ x y)

lemma mem_G1_iff (x : L1 G₀) (y : R1 G₀) : y ∈ G1 G₀ x ↔ adj1Prop G₀ x y := by
  classical
  simp [G1]

lemma portEdgeL_inj (u : Fin (q₀ + 1)) : Function.Injective (portEdgeL G₀ u) := by
  intro a b hab
  have h1 : (enumL G₀ u a).1 = (enumL G₀ u b).1 := congrArg (fun e : GEdge G₀ => e.1.2) hab
  exact (enumL G₀ u).injective (Subtype.ext h1)

lemma portEdgeR_inj (v : Fin q₀) : Function.Injective (portEdgeR G₀ v) := by
  intro a b hab
  have h1 : (enumR G₀ v a).1 = (enumR G₀ v b).1 := congrArg (fun e : GEdge G₀ => e.1.1) hab
  exact (enumR G₀ v).injective (Subtype.ext h1)

lemma card_GEdge_sum_L : Fintype.card (GEdge G₀) = ∑ u : Fin (q₀ + 1), degL G₀ u :=
  card_genEdge_eq_sum_left G₀

lemma card_GEdge_sum_R : Fintype.card (GEdge G₀) = ∑ v : Fin q₀, degR G₀ v :=
  card_genEdge_eq_sum_right G₀

lemma subcubic_card_LR
    (hL2 : ∀ u, 2 ≤ (G₀ u).card) (hR2 : ∀ v, 2 ≤ (rightNbrs G₀ v).card) :
    Fintype.card (L1 G₀) = Fintype.card (R1 G₀) + 1 := by
  simp only [L1, R1, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]
  have hsumL : ∑ u : Fin (q₀ + 1), (degL G₀ u - 1) + (q₀ + 1) = ∑ u : Fin (q₀ + 1), degL G₀ u := by
    have h1 : ∑ u : Fin (q₀ + 1), ((degL G₀ u - 1) + 1) = ∑ u : Fin (q₀ + 1), degL G₀ u := by
      refine Finset.sum_congr rfl (fun u _ => ?_)
      have := hL2 u; unfold degL; omega
    rw [Finset.sum_add_distrib] at h1
    simpa using h1
  have hsumR : ∑ v : Fin q₀, (degR G₀ v - 1) + q₀ = ∑ v : Fin q₀, degR G₀ v := by
    have h1 : ∑ v : Fin q₀, ((degR G₀ v - 1) + 1) = ∑ v : Fin q₀, degR G₀ v := by
      refine Finset.sum_congr rfl (fun v _ => ?_)
      have := hR2 v; unfold degR; omega
    rw [Finset.sum_add_distrib] at h1
    simpa using h1
  have hE : ∑ u : Fin (q₀ + 1), degL G₀ u = ∑ v : Fin q₀, degR G₀ v := by
    rw [← card_GEdge_sum_L, ← card_GEdge_sum_R]
  omega

lemma subcubic_degL (hL2 : ∀ u, 2 ≤ (G₀ u).card) (hR2 : ∀ v, 2 ≤ (rightNbrs G₀ v).card) :
    (∀ x : L1 G₀, 2 ≤ (G1 G₀ x).card ∧ (G1 G₀ x).card ≤ 3) ∧
    (∀ u : Fin (q₀ + 1), (G1 G₀ (Sum.inl ⟨u, ⟨0, by have := hL2 u; unfold degL; omega⟩⟩)).card = 2) ∧
    Fintype.card (GenEdge (G1 G₀)) = 5 * Fintype.card (GEdge G₀) - 4 * q₀ - 2 := by
  classical
  have hcard_inl : ∀ u (j : Fin (degL G₀ u)),
      (G1 G₀ (Sum.inl ⟨u, j⟩)).card =
        1 + (if j.val < degL G₀ u - 1 then 1 else 0) + (if 0 < j.val then 1 else 0) := by
    intro u j
    let v0 : Fin q₀ := (enumL G₀ u j).1
    have hu_in : u ∈ rightNbrs G₀ v0 := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (enumL G₀ u j).2⟩
    let j0' : Fin (degR G₀ v0) := (enumR G₀ v0).symm ⟨u, hu_in⟩
    let sOrig : Finset (R1 G₀) := {Sum.inl ⟨v0, j0'⟩}
    let sR : Finset (R1 G₀) := if h : j.val < degL G₀ u - 1 then {Sum.inr ⟨u, ⟨j.val, h⟩⟩} else ∅
    let sL : Finset (R1 G₀) := if h : 0 < j.val then {Sum.inr ⟨u, ⟨j.val - 1, by omega⟩⟩} else ∅
    have heq : G1 G₀ (Sum.inl ⟨u, j⟩) = sOrig ∪ (sR ∪ sL) := by
      ext y
      rw [mem_G1_iff]
      rcases y with ⟨v, j'⟩ | ⟨u', t⟩
      · simp only [adj1Prop, sOrig, Finset.mem_union, Finset.mem_singleton]
        have hnotR : Sum.inl ⟨v, j'⟩ ∉ sR := by
          dsimp [sR]; split_ifs <;> simp
        have hnotL : Sum.inl ⟨v, j'⟩ ∉ sL := by
          dsimp [sL]; split_ifs <;> simp
        simp only [hnotR, hnotL, or_false]
        constructor
        · rintro ⟨rfl, hu'⟩
          congr 1; refine Sigma.ext rfl (heq_of_eq ?_)
          apply (enumR G₀ v0).injective
          have hjeq : (enumR G₀ v0 j0').1 = u := by simp [j0', v0]
          exact Subtype.ext (hu'.trans hjeq.symm)
        · intro h
          injection h with hsig
          cases hsig
          exact ⟨rfl, by simp [j0', v0]⟩
      · simp only [adj1Prop, sOrig, Finset.mem_union, Finset.mem_singleton, reduceCtorEq, false_or]
        constructor
        · rintro ⟨rfl, hjt | hjt⟩
          · left
            have hlt : j.val < degL G₀ u - 1 := by omega
            simp only [sR, hlt, ↓reduceDIte, Finset.mem_singleton]
            congr 1; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext hjt.symm
          · right
            have hpos : 0 < j.val := by omega
            simp only [sL, hpos, ↓reduceDIte, Finset.mem_singleton]
            congr 1; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext (by (try dsimp); omega)
        · rintro (hR | hL)
          · by_cases hlt : j.val < degL G₀ u - 1
            · simp only [sR, hlt, ↓reduceDIte, Finset.mem_singleton] at hR
              injection hR with hsig
              rcases Sigma.mk.inj hsig with ⟨rfl, hteq⟩
              exact ⟨rfl, Or.inl (congrArg Fin.val (eq_of_heq hteq)).symm⟩
            · simp [sR, hlt] at hR
          · by_cases hpos : 0 < j.val
            · simp only [sL, hpos, ↓reduceDIte, Finset.mem_singleton] at hL
              injection hL with hsig
              rcases Sigma.mk.inj hsig with ⟨rfl, hteq⟩
              have hv := congrArg Fin.val (eq_of_heq hteq)
              exact ⟨rfl, Or.inr (by dsimp at hv; omega)⟩
            · simp [sL, hpos] at hL
    have hd1 : Disjoint sOrig (sR ∪ sL) := by
      rw [Finset.disjoint_left]
      intro y hy1 hy2
      rw [Finset.mem_singleton.mp hy1] at hy2
      rcases Finset.mem_union.mp hy2 with h | h <;> (dsimp [sR, sL] at h; split_ifs at h <;> simp at h)
    have hd2 : Disjoint sR sL := by
      rw [Finset.disjoint_left]
      intro y hy1 hy2
      dsimp [sR] at hy1; dsimp [sL] at hy2
      split_ifs at hy1 hy2 <;> simp at hy1 hy2
      subst hy1
      injection hy2 with hsig
      have hv := congrArg Fin.val (eq_of_heq (Sigma.mk.inj hsig).2)
      dsimp at hv; omega
    rw [heq, Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hd2]
    have hc0 : sOrig.card = 1 := Finset.card_singleton _
    have hc1 : sR.card = if j.val < degL G₀ u - 1 then 1 else 0 := by
      dsimp [sR]; split_ifs <;> simp
    have hc2 : sL.card = if 0 < j.val then 1 else 0 := by
      dsimp [sL]; split_ifs <;> simp
    rw [hc0, hc1, hc2]; omega
  have hcard_inr : ∀ v (t : Fin (degR G₀ v - 1)), (G1 G₀ (Sum.inr ⟨v, t⟩)).card = 2 := by
    intro v t
    have ht1 : t.val < degR G₀ v := by omega
    have ht2 : t.val + 1 < degR G₀ v := by omega
    let y1 : R1 G₀ := Sum.inl ⟨v, ⟨t.val, ht1⟩⟩
    let y2 : R1 G₀ := Sum.inl ⟨v, ⟨t.val + 1, ht2⟩⟩
    have hne : y1 ≠ y2 := by
      intro h; injection h with hsig
      have hv := congrArg Fin.val (eq_of_heq (Sigma.mk.inj hsig).2)
      dsimp at hv; omega
    have heq : G1 G₀ (Sum.inr ⟨v, t⟩) = {y1, y2} := by
      ext y
      rw [mem_G1_iff]
      rcases y with ⟨v', j⟩ | ⟨u', t'⟩
      · simp only [adj1Prop, y1, y2, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl, h1 | h2⟩
          · left; congr 1; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext h1
          · right; congr 1; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext h2
        · rintro (h | h)
          · injection h with hsig; rcases Sigma.mk.inj hsig with ⟨rfl, hjeq⟩
            exact ⟨rfl, Or.inl (congrArg Fin.val (eq_of_heq hjeq))⟩
          · injection h with hsig; rcases Sigma.mk.inj hsig with ⟨rfl, hjeq⟩
            exact ⟨rfl, Or.inr (congrArg Fin.val (eq_of_heq hjeq))⟩
      · simp [adj1Prop, y1, y2]
    rw [heq, Finset.card_pair hne]
  refine ⟨?_, ?_, ?_⟩
  · rintro (⟨u, j⟩ | ⟨v, t⟩)
    · rw [hcard_inl u j]
      have hd := hL2 u; unfold degL at j ⊢
      split_ifs <;> omega
    · rw [hcard_inr v t]; omega
  · intro u
    rw [hcard_inl u ⟨0, _⟩]
    have hd := hL2 u; unfold degL at ⊢
    simp [show 0 < (G₀ u).card - 1 by omega]
  · rw [card_genEdge_eq_sum_left, Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_sigma]
    have hsum1 : ∑ u : Fin (q₀ + 1), ∑ j : Fin (degL G₀ u), (G1 G₀ (Sum.inl ⟨u, j⟩)).card =
        3 * Fintype.card (GEdge G₀) - 2 * (q₀ + 1) := by
      have hper : ∀ u : Fin (q₀ + 1),
          ∑ j : Fin (degL G₀ u), (G1 G₀ (Sum.inl ⟨u, j⟩)).card = 3 * degL G₀ u - 2 := by
        intro u
        simp_rw [hcard_inl u]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        have h1 : ∑ _j : Fin (degL G₀ u), 1 = degL G₀ u := by simp
        have h2 : ∑ j : Fin (degL G₀ u), (if j.val < degL G₀ u - 1 then 1 else 0) = degL G₀ u - 1 := by
          rw [Finset.sum_boole, Nat.cast_id]
          have hdu_lt : degL G₀ u - 1 < degL G₀ u := by have := hL2 u; unfold degL; omega
          have hfilt : (Finset.univ.filter (fun j : Fin (degL G₀ u) => j.val < degL G₀ u - 1)) =
              Finset.univ.erase ⟨degL G₀ u - 1, hdu_lt⟩ := by
            ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_true, Finset.mem_erase, ne_eq, Fin.ext_iff]
            have := j.isLt; omega
          rw [hfilt, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
        have h3 : ∑ j : Fin (degL G₀ u), (if 0 < j.val then 1 else 0) = degL G₀ u - 1 := by
          rw [Finset.sum_boole, Nat.cast_id]
          have hdu_pos : 0 < degL G₀ u := by have := hL2 u; unfold degL; omega
          have hfilt : (Finset.univ.filter (fun j : Fin (degL G₀ u) => 0 < j.val)) =
              Finset.univ.erase ⟨0, hdu_pos⟩ := by
            ext j; simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_true, Finset.mem_erase, ne_eq, Fin.ext_iff]
            omega
          rw [hfilt, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
        rw [h1, h2, h3]
        have := hL2 u; unfold degL; omega
      simp_rw [hper]
      have htot : ∑ u : Fin (q₀ + 1), (3 * degL G₀ u - 2) + 2 * (q₀ + 1) =
          3 * ∑ u : Fin (q₀ + 1), degL G₀ u := by
        have h1 : ∑ u : Fin (q₀ + 1), ((3 * degL G₀ u - 2) + 2) =
            ∑ u : Fin (q₀ + 1), 3 * degL G₀ u := by
          refine Finset.sum_congr rfl (fun u _ => ?_)
          have := hL2 u; unfold degL; omega
        rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h1
        simpa [mul_comm] using h1
      rw [← card_GEdge_sum_L] at htot
      omega
    have hsum2 : ∑ v : Fin q₀, ∑ t : Fin (degR G₀ v - 1), (G1 G₀ (Sum.inr ⟨v, t⟩)).card =
        2 * Fintype.card (GEdge G₀) - 2 * q₀ := by
      simp_rw [hcard_inr]
      have h1 : ∑ v : Fin q₀, ∑ _t : Fin (degR G₀ v - 1), 2 =
          ∑ v : Fin q₀, 2 * (degR G₀ v - 1) := by
        refine Finset.sum_congr rfl (fun v _ => by simp [mul_comm])
      rw [h1]
      have htot : ∑ v : Fin q₀, 2 * (degR G₀ v - 1) + 2 * q₀ = 2 * ∑ v : Fin q₀, degR G₀ v := by
        have h2 : ∑ v : Fin q₀, (2 * (degR G₀ v - 1) + 2) = ∑ v : Fin q₀, 2 * degR G₀ v := by
          refine Finset.sum_congr rfl (fun v _ => ?_)
          have := hR2 v; unfold degR; omega
        rw [Finset.sum_add_distrib] at h2
        rw [Finset.mul_sum]
        simpa [mul_comm] using h2
      rw [← card_GEdge_sum_R] at htot
      omega
    rw [hsum1, hsum2]
    have hge : 2 * (q₀ + 1) ≤ Fintype.card (GEdge G₀) := by
      rw [card_GEdge_sum_L]
      calc 2 * (q₀ + 1) = ∑ _u : Fin (q₀ + 1), 2 := by simp [mul_comm]
        _ ≤ ∑ u : Fin (q₀ + 1), degL G₀ u := Finset.sum_le_sum (fun u _ => hL2 u)
    omega

lemma subcubic_degR (hL2 : ∀ u, 2 ≤ (G₀ u).card) (hR2 : ∀ v, 2 ≤ (rightNbrs G₀ v).card) :
    (∀ y : R1 G₀, 2 ≤ (gRightNbrs (G1 G₀) y).card ∧ (gRightNbrs (G1 G₀) y).card ≤ 3) ∧
    (∀ u : Fin (q₀ + 1), (gRightNbrs (G1 G₀) (Sum.inr ⟨u, ⟨0, by have := hL2 u; unfold degL; omega⟩⟩)).card = 2) := by
  classical
  have hcard_inl : ∀ v (j : Fin (degR G₀ v)),
      (gRightNbrs (G1 G₀) (Sum.inl ⟨v, j⟩)).card =
        1 + (if j.val < degR G₀ v - 1 then 1 else 0) + (if 0 < j.val then 1 else 0) := by
    intro v j
    let u0 : Fin (q₀ + 1) := (enumR G₀ v j).1
    have hv_in : v ∈ G₀ u0 := (Finset.mem_filter.mp (enumR G₀ v j).2).2
    let j0' : Fin (degL G₀ u0) := (enumL G₀ u0).symm ⟨v, hv_in⟩
    let sOrig : Finset (L1 G₀) := {Sum.inl ⟨u0, j0'⟩}
    let sR : Finset (L1 G₀) := if h : j.val < degR G₀ v - 1 then {Sum.inr ⟨v, ⟨j.val, h⟩⟩} else ∅
    let sL : Finset (L1 G₀) := if h : 0 < j.val then {Sum.inr ⟨v, ⟨j.val - 1, by omega⟩⟩} else ∅
    have heq : gRightNbrs (G1 G₀) (Sum.inl ⟨v, j⟩) = sOrig ∪ (sR ∪ sL) := by
      ext x
      simp only [gRightNbrs, Finset.mem_filter, Finset.mem_univ, true_and, mem_G1_iff]
      rcases x with ⟨u, j'⟩ | ⟨v', t⟩
      · simp only [adj1Prop, sOrig, Finset.mem_union, Finset.mem_singleton]
        have hnotR : Sum.inl ⟨u, j'⟩ ∉ sR := by dsimp [sR]; split_ifs <;> simp
        have hnotL : Sum.inl ⟨u, j'⟩ ∉ sL := by dsimp [sL]; split_ifs <;> simp
        simp only [hnotR, hnotL, or_false]
        constructor
        · rintro ⟨hv', rfl⟩
          congr 1; refine Sigma.ext rfl (heq_of_eq ?_)
          apply (enumL G₀ u0).injective
          have hjeq : (enumL G₀ u0 j0').1 = v := by simp [j0', u0]
          exact Subtype.ext (hv'.trans hjeq.symm)
        · intro h
          injection h with hsig
          cases hsig
          exact ⟨by simp [j0', u0], rfl⟩
      · simp only [adj1Prop, sOrig, Finset.mem_union, Finset.mem_singleton, reduceCtorEq, false_or]
        constructor
        · rintro ⟨rfl, hjt | hjt⟩
          · left
            have hlt : j.val < degR G₀ v - 1 := by omega
            simp only [sR, hlt, ↓reduceDIte, Finset.mem_singleton]
            congr 1; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext hjt.symm
          · right
            have hpos : 0 < j.val := by omega
            simp only [sL, hpos, ↓reduceDIte, Finset.mem_singleton]
            congr 1; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext (by (try dsimp); omega)
        · rintro (hR | hL)
          · by_cases hlt : j.val < degR G₀ v - 1
            · simp only [sR, hlt, ↓reduceDIte, Finset.mem_singleton] at hR
              injection hR with hsig
              rcases Sigma.mk.inj hsig with ⟨rfl, hteq⟩
              exact ⟨rfl, Or.inl (congrArg Fin.val (eq_of_heq hteq)).symm⟩
            · simp [sR, hlt] at hR
          · by_cases hpos : 0 < j.val
            · simp only [sL, hpos, ↓reduceDIte, Finset.mem_singleton] at hL
              injection hL with hsig
              rcases Sigma.mk.inj hsig with ⟨rfl, hteq⟩
              have hv := congrArg Fin.val (eq_of_heq hteq)
              exact ⟨rfl, Or.inr (by dsimp at hv; omega)⟩
            · simp [sL, hpos] at hL
    have hd1 : Disjoint sOrig (sR ∪ sL) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [Finset.mem_singleton.mp hx1] at hx2
      rcases Finset.mem_union.mp hx2 with h | h <;> (dsimp [sR, sL] at h; split_ifs at h <;> simp at h)
    have hd2 : Disjoint sR sL := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      dsimp [sR] at hx1; dsimp [sL] at hx2
      split_ifs at hx1 hx2 <;> simp at hx1 hx2
      subst hx1
      injection hx2 with hsig
      have hv := congrArg Fin.val (eq_of_heq (Sigma.mk.inj hsig).2)
      dsimp at hv; omega
    rw [heq, Finset.card_union_of_disjoint hd1, Finset.card_union_of_disjoint hd2]
    have hc0 : sOrig.card = 1 := Finset.card_singleton _
    have hc1 : sR.card = if j.val < degR G₀ v - 1 then 1 else 0 := by dsimp [sR]; split_ifs <;> simp
    have hc2 : sL.card = if 0 < j.val then 1 else 0 := by dsimp [sL]; split_ifs <;> simp
    rw [hc0, hc1, hc2]; omega
  have hcard_inr : ∀ u (t : Fin (degL G₀ u - 1)), (gRightNbrs (G1 G₀) (Sum.inr ⟨u, t⟩)).card = 2 := by
    intro u t
    have ht1 : t.val < degL G₀ u := by omega
    have ht2 : t.val + 1 < degL G₀ u := by omega
    let x1 : L1 G₀ := Sum.inl ⟨u, ⟨t.val, ht1⟩⟩
    let x2 : L1 G₀ := Sum.inl ⟨u, ⟨t.val + 1, ht2⟩⟩
    have hne : x1 ≠ x2 := by
      intro h; injection h with hsig
      have hv := congrArg Fin.val (eq_of_heq (Sigma.mk.inj hsig).2)
      dsimp at hv; omega
    have heq : gRightNbrs (G1 G₀) (Sum.inr ⟨u, t⟩) = {x1, x2} := by
      ext x
      simp only [gRightNbrs, Finset.mem_filter, Finset.mem_univ, true_and, mem_G1_iff]
      rcases x with ⟨u', j⟩ | ⟨v', t'⟩
      · simp only [adj1Prop, x1, x2, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl, h1 | h2⟩
          · left; congr 1; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext h1
          · right; congr 1; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext h2
        · rintro (h | h)
          · injection h with hsig; rcases Sigma.mk.inj hsig with ⟨rfl, hjeq⟩
            exact ⟨rfl, Or.inl (congrArg Fin.val (eq_of_heq hjeq))⟩
          · injection h with hsig; rcases Sigma.mk.inj hsig with ⟨rfl, hjeq⟩
            exact ⟨rfl, Or.inr (congrArg Fin.val (eq_of_heq hjeq))⟩
      · simp [adj1Prop, x1, x2]
    rw [heq, Finset.card_pair hne]
  refine ⟨?_, ?_⟩
  · rintro (⟨v, j⟩ | ⟨u, t⟩)
    · rw [hcard_inl v j]
      have hd := hR2 v; unfold degR at j ⊢
      split_ifs <;> omega
    · rw [hcard_inr u t]; omega
  · intro u
    exact hcard_inr u ⟨0, _⟩

lemma subcubic_conn (hL2 : ∀ u, 2 ≤ (G₀ u).card) (hR2 : ∀ v, 2 ≤ (rightNbrs G₀ v).card)
    (hconn : ∀ f : Fin (q₀ + 1) ⊕ Fin q₀ → Bool,
      (∀ u, ∀ v ∈ G₀ u, f (Sum.inl u) = f (Sum.inr v)) → ∀ x y, f x = f y) :
    GenConn (G1 G₀) := by
  intro f hf
  have hL_const : ∀ u (j : Fin (degL G₀ u)),
      f (Sum.inl (Sum.inl ⟨u, j⟩)) = f (Sum.inl (Sum.inl ⟨u, ⟨0, by have := hL2 u; unfold degL; omega⟩⟩)) := by
    intro u j
    rcases j with ⟨j, hj⟩
    induction j with
    | zero => rfl
    | succ j ih =>
      have hj1 : j < degL G₀ u - 1 := by omega
      have h1 := hf (Sum.inl ⟨u, ⟨j, by omega⟩⟩) (Sum.inr ⟨u, ⟨j, hj1⟩⟩)
        ((mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inl rfl⟩)
      have h2 := hf (Sum.inl ⟨u, ⟨j + 1, hj⟩⟩) (Sum.inr ⟨u, ⟨j, hj1⟩⟩)
        ((mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inr rfl⟩)
      exact h2.trans (h1.symm.trans (ih (by omega)))
  have hR_const : ∀ v (j : Fin (degR G₀ v)),
      f (Sum.inr (Sum.inl ⟨v, j⟩)) = f (Sum.inr (Sum.inl ⟨v, ⟨0, by have := hR2 v; unfold degR; omega⟩⟩)) := by
    intro v j
    rcases j with ⟨j, hj⟩
    induction j with
    | zero => rfl
    | succ j ih =>
      have hj1 : j < degR G₀ v - 1 := by omega
      have h1 := hf (Sum.inr ⟨v, ⟨j, hj1⟩⟩) (Sum.inl ⟨v, ⟨j, by omega⟩⟩)
        ((mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inl rfl⟩)
      have h2 := hf (Sum.inr ⟨v, ⟨j, hj1⟩⟩) (Sum.inl ⟨v, ⟨j + 1, hj⟩⟩)
        ((mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inr rfl⟩)
      exact h2.symm.trans (h1.trans (ih (by omega)))
  let f₀ : Fin (q₀ + 1) ⊕ Fin q₀ → Bool := fun z => match z with
    | Sum.inl u => f (Sum.inl (Sum.inl ⟨u, ⟨0, by have := hL2 u; unfold degL; omega⟩⟩))
    | Sum.inr v => f (Sum.inr (Sum.inl ⟨v, ⟨0, by have := hR2 v; unfold degR; omega⟩⟩))
  have hf₀ : ∀ u, ∀ v ∈ G₀ u, f₀ (Sum.inl u) = f₀ (Sum.inr v) := by
    intro u v hv
    let jL := (enumL G₀ u).symm ⟨v, hv⟩
    let jR := (enumR G₀ v).symm ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩⟩
    have hedge : adj1Prop G₀ (Sum.inl ⟨u, jL⟩) (Sum.inl ⟨v, jR⟩) := by
      simp [adj1Prop, jL, jR]
    have h1 := hf (Sum.inl ⟨u, jL⟩) (Sum.inl ⟨v, jR⟩) ((mem_G1_iff G₀ _ _).mpr hedge)
    rw [hL_const u jL, hR_const v jR] at h1
    exact h1
  have hval : ∀ z : L1 G₀ ⊕ R1 G₀, f z = f₀ (Sum.inl ⟨0, Nat.succ_pos q₀⟩) := by
    rintro ((⟨u, j⟩ | ⟨v, t⟩) | (⟨v, j⟩ | ⟨u, t⟩))
    · rw [hL_const u j]; exact hconn f₀ hf₀ (Sum.inl u) (Sum.inl ⟨0, Nat.succ_pos q₀⟩)
    · have h1 := hf (Sum.inr ⟨v, t⟩) (Sum.inl ⟨v, ⟨t.val, by omega⟩⟩)
        ((mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inl rfl⟩)
      rw [h1, hR_const v]; exact hconn f₀ hf₀ (Sum.inr v) (Sum.inl ⟨0, Nat.succ_pos q₀⟩)
    · rw [hR_const v j]; exact hconn f₀ hf₀ (Sum.inr v) (Sum.inl ⟨0, Nat.succ_pos q₀⟩)
    · have h1 := hf (Sum.inl ⟨u, ⟨t.val, by omega⟩⟩) (Sum.inr ⟨u, t⟩)
        ((mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inl rfl⟩)
      rw [← h1, hL_const u]; exact hconn f₀ hf₀ (Sum.inl u) (Sum.inl ⟨0, Nat.succ_pos q₀⟩)
  intro x y
  rw [hval x, hval y]

set_option maxHeartbeats 1000000 in
lemma subcubic_girth (a : ℕ) (us : Fin (a + 2) ↪ L1 G₀) (vs : Fin (a + 2) ↪ R1 G₀)
    (hcyc : ∀ i, vs i ∈ G1 G₀ (us i) ∧ vs i ∈ G1 G₀ (us (i + 1))) :
    ∃ (a₀ : ℕ) (us₀ : Fin (a₀ + 2) ↪ Fin (q₀ + 1)) (vs₀ : Fin (a₀ + 2) ↪ Fin q₀),
      a₀ + 2 ≤ a + 2 ∧ ∀ i, vs₀ i ∈ G₀ (us₀ i) ∧ vs₀ i ∈ G₀ (us₀ (i + 1)) := by
  classical
  let M := 2 * (a + 2)
  have hM4 : 4 ≤ M := by omega
  haveI : NeZero M := ⟨by omega⟩
  let w : Fin M → L1 G₀ ⊕ R1 G₀ := fun r =>
    if r.val % 2 = 0 then Sum.inl (us ⟨r.val / 2, by omega⟩)
    else Sum.inr (vs ⟨r.val / 2, by omega⟩)
  have hw_inj : Function.Injective w := by
    intro r1 r2 heq
    dsimp only [w] at heq
    by_cases h1 : r1.val % 2 = 0 <;> by_cases h2 : r2.val % 2 = 0
    · simp only [h1, h2, ↓reduceIte, Sum.inl.injEq] at heq
      have hdiv := congrArg Fin.val (us.injective heq); dsimp at hdiv; exact Fin.ext (by omega)
    · simp [h1, h2] at heq
    · simp [h1, h2] at heq
    · simp only [h1, h2, ↓reduceIte, Sum.inr.injEq] at heq
      have hdiv := congrArg Fin.val (vs.injective heq); dsimp at hdiv; exact Fin.ext (by omega)
  let adjU : L1 G₀ ⊕ R1 G₀ → L1 G₀ ⊕ R1 G₀ → Prop := fun x y =>
    match x, y with
    | Sum.inl l, Sum.inr r => adj1Prop G₀ l r
    | Sum.inr r, Sum.inl l => adj1Prop G₀ l r
    | _, _ => False
  have hadjU_symm : ∀ x y, adjU x y → adjU y x := by
    rintro (l | r) (l' | r') h <;> exact h
  have hw_adj : ∀ r : Fin M, adjU (w r) (w (r + 1)) := by
    intro r
    have hrm : (r + 1).val = (r.val + 1) % M := by simp [Fin.val_add, Fin.val_one']
    by_cases h0 : r.val % 2 = 0
    · have hlt : r.val + 1 < M := by omega
      have h1 : (r + 1).val = r.val + 1 := by rw [hrm, Nat.mod_eq_of_lt hlt]
      have hdiv : (r + 1).val / 2 = r.val / 2 := by omega
      have hmod : (r + 1).val % 2 ≠ 0 := by omega
      simp only [w, h0, ↓reduceIte, hmod, adjU]
      have hidx : (⟨(r + 1).val / 2, by omega⟩ : Fin (a + 2)) = ⟨r.val / 2, by omega⟩ := Fin.ext hdiv
      rw [hidx]
      exact (mem_G1_iff G₀ _ _).mp (hcyc ⟨r.val / 2, by omega⟩).1
    · have hmod : (r + 1).val % 2 = 0 := by
        rw [hrm]
        by_cases hlt : r.val + 1 < M
        · rw [Nat.mod_eq_of_lt hlt]; omega
        · have : r.val + 1 = M := by omega
          rw [this, Nat.mod_self]
      simp only [w, h0, ↓reduceIte, hmod, adjU]
      have hidx : (⟨(r + 1).val / 2, by have := (r + 1).isLt; omega⟩ : Fin (a + 2)) = ⟨r.val / 2, by omega⟩ + 1 := by
        apply Fin.ext
        dsimp only
        rw [hrm]
        by_cases hlt : r.val + 1 < M
        · rw [Nat.mod_eq_of_lt hlt]
          have : r.val / 2 + 1 < a + 2 := by omega
          simp [Fin.val_add, Fin.val_one, Nat.mod_eq_of_lt this]; omega
        · have hrval : r.val + 1 = M := by omega
          rw [hrval, Nat.mod_self]
          have : r.val / 2 + 1 = a + 2 := by omega
          simp [Fin.val_add, Fin.val_one, this]
      rw [hidx]
      exact (mem_G1_iff G₀ _ _).mp (hcyc ⟨r.val / 2, by omega⟩).2
  let proj : L1 G₀ ⊕ R1 G₀ → Fin (q₀ + 1) ⊕ Fin q₀ := fun z =>
    match z with
    | Sum.inl (Sum.inl ⟨u, _⟩) => Sum.inl u
    | Sum.inl (Sum.inr ⟨v, _⟩) => Sum.inr v
    | Sum.inr (Sum.inl ⟨v, _⟩) => Sum.inr v
    | Sum.inr (Sum.inr ⟨u, _⟩) => Sum.inl u
  let ht : L1 G₀ ⊕ R1 G₀ → ℕ := fun z =>
    match z with
    | Sum.inl (Sum.inl ⟨_, j⟩) => 2 * j.val
    | Sum.inr (Sum.inr ⟨_, t⟩) => 2 * t.val + 1
    | Sum.inr (Sum.inl ⟨_, j⟩) => 2 * j.val
    | Sum.inl (Sum.inr ⟨_, t⟩) => 2 * t.val + 1
  have hht_inj : ∀ x y, proj x = proj y → ht x = ht y → x = y := by
    intro x y hpr hht
    rcases x with (⟨u1, j1⟩ | ⟨v1, t1⟩) | (⟨v1, j1⟩ | ⟨u1, t1⟩) <;>
    rcases y with (⟨u2, j2⟩ | ⟨v2, t2⟩) | (⟨v2, j2⟩ | ⟨u2, t2⟩) <;>
    simp only [proj, ht, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at hpr hht
    all_goals try omega
    all_goals try subst hpr
    · congr 2; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext (by (try dsimp); omega)
    · congr 2; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext (by (try dsimp); omega)
    · congr 2; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext (by (try dsimp); omega)
    · congr 2; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext (by (try dsimp); omega)
  have hspacer_ht : ∀ x y, adjU x y → proj x = proj y → ht x = ht y + 1 ∨ ht y = ht x + 1 := by
    intro x y hadj hpr
    rcases x with (⟨u1, j1⟩ | ⟨v1, t1⟩) | (⟨v1, j1⟩ | ⟨u1, t1⟩) <;>
    rcases y with (⟨u2, j2⟩ | ⟨v2, t2⟩) | (⟨v2, j2⟩ | ⟨u2, t2⟩) <;>
    simp only [adjU, adj1Prop, proj, ht, reduceCtorEq] at hadj hpr ⊢
    all_goals try exact False.elim hadj
    · rcases hadj with ⟨_, h1 | h2⟩ <;> omega
    · rcases hadj with ⟨_, h1 | h2⟩ <;> omega
    · rcases hadj with ⟨_, h1 | h2⟩ <;> omega
    · rcases hadj with ⟨_, h1 | h2⟩ <;> omega
  have hex_orig : ∃ r : Fin M, proj (w r) ≠ proj (w (r + 1)) := by
    by_contra hno
    push Not at hno
    have hconst : ∀ r : Fin M, proj (w r) = proj (w ⟨0, by omega⟩) := by
      intro r
      rcases r with ⟨r, hr⟩
      induction r with
      | zero => rfl
      | succ r ih =>
        have hstep := hno ⟨r, by omega⟩
        have h1 : (⟨r, by omega⟩ : Fin M) + 1 = ⟨r + 1, hr⟩ := by
          apply Fin.ext; simp [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt hr]
        rw [h1] at hstep
        exact hstep.symm.trans (ih (by omega))
    obtain ⟨r0, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun r : Fin M => ht (w r))
      ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    have h1 := hspacer_ht (w r0) (w (r0 + 1)) (hw_adj r0) (hno r0)
    have h2 := hspacer_ht (w (r0 - 1)) (w r0) (by simpa using hw_adj (r0 - 1))
      (by simpa using hno (r0 - 1))
    have hm1 := hmax (r0 + 1) (Finset.mem_univ _)
    have hm2 := hmax (r0 - 1) (Finset.mem_univ _)
    have hht_eq : ht (w (r0 - 1)) = ht (w (r0 + 1)) := by omega
    have hweq : w (r0 - 1) = w (r0 + 1) :=
      hht_inj _ _ ((hconst _).trans (hconst _).symm) hht_eq
    have hreq : r0 - 1 = r0 + 1 := hw_inj hweq
    exact fin_sub_one_ne_add_one (by omega : 3 ≤ M) r0 hreq
  have horig_sides : ∀ x y, adjU x y → proj x ≠ proj y →
      (∃ u v, proj x = Sum.inl u ∧ proj y = Sum.inr v ∧ v ∈ G₀ u ∧
        (∃ j j', x = Sum.inl (Sum.inl ⟨u, j⟩) ∧ y = Sum.inr (Sum.inl ⟨v, j'⟩))) ∨
      (∃ u v, proj x = Sum.inr v ∧ proj y = Sum.inl u ∧ v ∈ G₀ u ∧
        (∃ j j', x = Sum.inr (Sum.inl ⟨v, j'⟩) ∧ y = Sum.inl (Sum.inl ⟨u, j⟩))) := by
    intro x y hadj hne
    rcases x with (⟨u1, j1⟩ | ⟨v1, t1⟩) | (⟨v1, j1⟩ | ⟨u1, t1⟩) <;>
    rcases y with (⟨u2, j2⟩ | ⟨v2, t2⟩) | (⟨v2, j2⟩ | ⟨u2, t2⟩) <;>
    simp only [adjU, adj1Prop, proj] at hadj hne ⊢
    all_goals try exact False.elim hadj
    · rcases hadj with ⟨hv, hu⟩
      left; refine ⟨u1, v2, rfl, rfl, ?_, j1, j2, rfl, rfl⟩
      rw [← hv]; exact (enumL G₀ u1 j1).2
    · exact absurd (congrArg Sum.inl hadj.1) hne
    · exact absurd (congrArg Sum.inr hadj.1.symm) hne
    · rcases hadj with ⟨hv, hu⟩
      right; refine ⟨u2, v1, rfl, rfl, ?_, j2, j1, rfl, rfl⟩
      rw [← hv]; exact (enumL G₀ u2 j2).2
    · exact absurd (congrArg Sum.inr hadj.1) hne
    · exact absurd (congrArg Sum.inl hadj.1.symm) hne
  have horig_unique : ∀ r1 r2 : Fin M, proj (w r1) ≠ proj (w (r1 + 1)) →
      proj (w r2) ≠ proj (w (r2 + 1)) →
      ({proj (w r1), proj (w (r1 + 1))} : Finset _) = {proj (w r2), proj (w (r2 + 1))} →
      r1 = r2 := by
    intro r1 r2 hne1 hne2 hset
    have huniq_edge : ∀ u v (x1 y1 x2 y2 : L1 G₀ ⊕ R1 G₀),
        adjU x1 y1 → adjU x2 y2 →
        proj x1 = Sum.inl u → proj y1 = Sum.inr v →
        proj x2 = Sum.inl u → proj y2 = Sum.inr v →
        x1 = x2 ∧ y1 = y2 := by
      intro u v x1 y1 x2 y2 ha1 ha2 hx1 hy1 hx2 hy2
      rcases horig_sides x1 y1 ha1 (by rw [hx1, hy1]; simp) with
        ⟨u1, v1, hu1, hv1, _, j1, j1', rfl, rfl⟩ | ⟨_, _, h1, _, _, _⟩
      · rcases horig_sides x2 y2 ha2 (by rw [hx2, hy2]; simp) with
          ⟨u2, v2, hu2, hv2, _, j2, j2', rfl, rfl⟩ | ⟨_, _, h2, _, _, _⟩
        · have hu1u : u1 = u := Sum.inl.inj (hu1.symm.trans hx1)
          have hv1v : v1 = v := Sum.inr.inj (hv1.symm.trans hy1)
          have hu2u : u2 = u := Sum.inl.inj (hu2.symm.trans hx2)
          have hv2v : v2 = v := Sum.inr.inj (hv2.symm.trans hy2)
          subst u1; subst v1; subst u2; subst v2
          simp only [adjU, adj1Prop] at ha1 ha2
          have hjL : j1 = j2 := (enumL G₀ u).injective (Subtype.ext (ha1.1.trans ha2.1.symm))
          have hjR : j1' = j2' := (enumR G₀ v).injective (Subtype.ext (ha1.2.trans ha2.2.symm))
          subst hjL; subst hjR; exact ⟨rfl, rfl⟩
        · rw [hx2] at h2; simp at h2
      · rw [hx1] at h1; simp at h1
    rcases horig_sides (w r1) (w (r1 + 1)) (hw_adj r1) hne1 with
      ⟨u1, v1, hu1, hv1, _, _⟩ | ⟨u1, v1, hv1, hu1, _, _⟩
    · rcases horig_sides (w r2) (w (r2 + 1)) (hw_adj r2) hne2 with
        ⟨u2, v2, hu2, hv2, _, _⟩ | ⟨u2, v2, hv2, hu2, _, _⟩
      · rw [hu1, hv1, hu2, hv2] at hset
        have hu12 : u1 = u2 := by
          have : Sum.inl u1 ∈ ({Sum.inl u2, Sum.inr v2} : Finset (Fin (q₀ + 1) ⊕ Fin q₀)) := by
            rw [← hset]; simp
          simp at this; exact this
        have hv12 : v1 = v2 := by
          have : Sum.inr v1 ∈ ({Sum.inl u2, Sum.inr v2} : Finset (Fin (q₀ + 1) ⊕ Fin q₀)) := by
            rw [← hset]; simp
          simp at this; exact this
        subst hu12; subst hv12
        exact hw_inj (huniq_edge u1 v1 _ _ _ _ (hw_adj r1) (hw_adj r2) hu1 hv1 hu2 hv2).1
      · rw [hu1, hv1, hu2, hv2] at hset
        have hu12 : u1 = u2 := by
          have : Sum.inl u1 ∈ ({Sum.inr v2, Sum.inl u2} : Finset (Fin (q₀ + 1) ⊕ Fin q₀)) := by
            rw [← hset]; simp
          simp at this; exact this
        have hv12 : v1 = v2 := by
          have : Sum.inr v1 ∈ ({Sum.inr v2, Sum.inl u2} : Finset (Fin (q₀ + 1) ⊕ Fin q₀)) := by
            rw [← hset]; simp
          simp at this; exact this
        subst hu12; subst hv12
        have hpair := huniq_edge u1 v1 (w r1) (w (r1 + 1)) (w (r2 + 1)) (w r2)
          (hw_adj r1) (hadjU_symm _ _ (hw_adj r2)) hu1 hv1 hu2 hv2
        have hr12 : r1 = r2 + 1 := hw_inj hpair.1
        have hr21 : r1 + 1 = r2 := hw_inj hpair.2
        exact False.elim (fin_add_two_ne_self (by omega : 3 ≤ M) r1 (by rw [hr21, ← hr12]))
    · rcases horig_sides (w r2) (w (r2 + 1)) (hw_adj r2) hne2 with
        ⟨u2, v2, hu2, hv2, _, _⟩ | ⟨u2, v2, hv2, hu2, _, _⟩
      · rw [hu1, hv1, hu2, hv2] at hset
        have hu12 : u1 = u2 := by
          have : Sum.inl u1 ∈ ({Sum.inl u2, Sum.inr v2} : Finset (Fin (q₀ + 1) ⊕ Fin q₀)) := by
            rw [← hset]; simp
          simp at this; exact this
        have hv12 : v1 = v2 := by
          have : Sum.inr v1 ∈ ({Sum.inl u2, Sum.inr v2} : Finset (Fin (q₀ + 1) ⊕ Fin q₀)) := by
            rw [← hset]; simp
          simp at this; exact this
        subst hu12; subst hv12
        have hpair := huniq_edge u1 v1 (w (r1 + 1)) (w r1) (w r2) (w (r2 + 1))
          (hadjU_symm _ _ (hw_adj r1)) (hw_adj r2) hu1 hv1 hu2 hv2
        have hr12 : r1 + 1 = r2 := hw_inj hpair.1
        have hr21 : r1 = r2 + 1 := hw_inj hpair.2
        exact False.elim (fin_add_two_ne_self (by omega : 3 ≤ M) r1 (by rw [hr12, ← hr21]))
      · rw [hu1, hv1, hu2, hv2] at hset
        have hu12 : u1 = u2 := by
          have : Sum.inl u1 ∈ ({Sum.inr v2, Sum.inl u2} : Finset (Fin (q₀ + 1) ⊕ Fin q₀)) := by
            rw [← hset]; simp
          simp at this; exact this
        have hv12 : v1 = v2 := by
          have : Sum.inr v1 ∈ ({Sum.inr v2, Sum.inl u2} : Finset (Fin (q₀ + 1) ⊕ Fin q₀)) := by
            rw [← hset]; simp
          simp at this; exact this
        subst hu12; subst hv12
        have hpair := huniq_edge u1 v1 (w (r1 + 1)) (w r1) (w (r2 + 1)) (w r2)
          (hadjU_symm _ _ (hw_adj r1)) (hadjU_symm _ _ (hw_adj r2)) hu1 hv1 hu2 hv2
        exact hw_inj hpair.2
  let S_orig : Finset (Fin M) := Finset.univ.filter (fun r => proj (w r) ≠ proj (w (r + 1)))
  have hS_ne : S_orig.Nonempty := by
    rcases hex_orig with ⟨r, hr⟩
    exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr⟩⟩
  let mTot := S_orig.card
  have hmTot_pos : 0 < mTot := Finset.card_pos.mpr hS_ne
  haveI : NeZero mTot := ⟨by omega⟩
  have hmTot_le : mTot ≤ M := by simpa [mTot] using Finset.card_le_univ S_orig
  let ord : Fin mTot ≃o S_orig := S_orig.orderIsoOfFin rfl
  let idx : Fin mTot → Fin M := fun t => (ord t).1
  have hidx_mem : ∀ t : Fin mTot, proj (w (idx t)) ≠ proj (w (idx t + 1)) := fun t =>
    (Finset.mem_filter.mp (ord t).2).2
  have hidx_mono : StrictMono idx := fun a b hab => ord.strictMono hab
  have hbetween : ∀ t : Fin mTot, proj (w (idx t + 1)) = proj (w (idx (t + 1))) := by
    intro t
    have hwalk : ∀ d : ℕ, (∀ s : ℕ, s < d →
        proj (w (idx t + 1 + ⟨s % M, Nat.mod_lt _ (by omega)⟩)) =
        proj (w (idx t + 1 + ⟨(s + 1) % M, Nat.mod_lt _ (by omega)⟩))) →
        proj (w (idx t + 1)) = proj (w (idx t + 1 + ⟨d % M, Nat.mod_lt _ (by omega)⟩)) := by
      intro d
      induction d with
      | zero => intro _; simp
      | succ d ih =>
        intro hstep
        rw [ih (fun s hs => hstep s (by omega))]
        exact hstep d (by omega)
    let a0 : Fin M := idx t + 1
    let gap := (idx (t + 1)).val + M - a0.val
    let d := gap % M
    have hdest : a0 + ⟨d % M, Nat.mod_lt _ (by omega)⟩ = idx (t + 1) := by
      apply Fin.ext
      simp only [Fin.val_add, d, gap, Nat.mod_mod]
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
      have h1 : a0.val + ((idx (t + 1)).val + M - a0.val) = (idx (t + 1)).val + M := by
        have := a0.isLt; omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (idx (t + 1)).isLt]
    rw [← hdest]
    apply hwalk d
    intro s hs
    have hstep1 : idx t + 1 + ⟨(s + 1) % M, Nat.mod_lt _ (by omega)⟩ =
        (idx t + 1 + ⟨s % M, Nat.mod_lt _ (by omega)⟩) + 1 := by
      apply Fin.ext
      simp only [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < M), Nat.add_mod_mod, Nat.mod_add_mod]
      congr 1
    rw [hstep1]
    by_contra hne
    let rcur := idx t + 1 + ⟨s % M, Nat.mod_lt _ (by omega)⟩
    have hcur_in : rcur ∈ S_orig := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
    let tcur : Fin mTot := ord.symm ⟨rcur, hcur_in⟩
    have hcur_eq : idx tcur = rcur := by
      dsimp only [idx, tcur]
      exact congrArg Subtype.val (ord.apply_symm_apply _)
    have hrcur_val : rcur.val = ((idx t).val + 1 + s) % M := by
      simp only [rcur, Fin.val_add, Fin.val_one']
      rw [Nat.mod_eq_of_lt (by omega : 1 < M)]
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, Nat.add_mod ((idx t).val + 1),
          Nat.mod_mod, ← Nat.add_mod]
    have hd_lt : d < M := Nat.mod_lt _ (by omega)
    by_cases htlast : t.val + 1 < mTot
    · have hlt_idx : (idx t).val < (idx (t + 1)).val := by
        have h1 : t < t + 1 := by
          change t.val < (t + 1).val
          rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < mTot), Nat.mod_eq_of_lt htlast]; omega
        exact hidx_mono h1
      have hd_eq : d = (idx (t + 1)).val - ((idx t).val + 1) := by
        have h1 : a0.val = (idx t).val + 1 := by
          simp only [a0, Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < M)]
          exact Nat.mod_eq_of_lt (by have := (idx (t + 1)).isLt; omega)
        simp only [d, gap, h1]
        have : (idx (t + 1)).val + M - ((idx t).val + 1) =
            ((idx (t + 1)).val - ((idx t).val + 1)) + M := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := (idx (t + 1)).isLt; omega)]
      have hrcur_eq : rcur.val = (idx t).val + 1 + s := by
        rw [hrcur_val, Nat.mod_eq_of_lt (by have := (idx (t + 1)).isLt; omega)]
      have hlt1 : idx t < idx tcur := by rw [hcur_eq]; change (idx t).val < rcur.val; omega
      have hlt2 : idx tcur < idx (t + 1) := by rw [hcur_eq]; change rcur.val < (idx (t + 1)).val; omega
      have ht1 : t < tcur := hidx_mono.lt_iff_lt.mp hlt1
      have ht2 : tcur < t + 1 := hidx_mono.lt_iff_lt.mp hlt2
      have htv : (t + 1).val = t.val + 1 := by
        rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < mTot), Nat.mod_eq_of_lt htlast]
      change t.val < tcur.val at ht1
      change tcur.val < (t + 1).val at ht2
      omega
    · have ht0 : t + 1 = ⟨0, hmTot_pos⟩ := by
        apply Fin.ext; simp only [Fin.val_add, Fin.val_one']
        by_cases hm2 : 1 < mTot
        · rw [Nat.mod_eq_of_lt hm2, show t.val + 1 = mTot by omega, Nat.mod_self]
        · have hm1 : mTot = 1 := by omega
          have ht0' : t.val = 0 := by omega
          simp [hm1, ht0']
      have hle_t : (idx ⟨0, hmTot_pos⟩).val ≤ (idx t).val := by
        by_cases h0 : (⟨0, hmTot_pos⟩ : Fin mTot) = t
        · rw [h0]
        · exact le_of_lt (hidx_mono (by change 0 < t.val; have := Fin.val_ne_of_ne h0; dsimp at this; omega))
      have hd_eq : d = M + (idx ⟨0, hmTot_pos⟩).val - ((idx t).val + 1) := by
        have hgap_rw : gap = (idx ⟨0, hmTot_pos⟩).val + M - a0.val := by
          change (idx (t + 1)).val + M - a0.val = _
          rw [ht0]
        by_cases hwrap : (idx t).val + 1 < M
        · have h1 : a0.val = (idx t).val + 1 := by
            simp only [a0, Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < M), Nat.mod_eq_of_lt hwrap]
          simp only [d, hgap_rw, h1]
          rw [Nat.mod_eq_of_lt (by omega)]; omega
        · have hmax_t : (idx t).val + 1 = M := by have := (idx t).isLt; omega
          have h1 : a0.val = 0 := by
            simp only [a0, Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < M), hmax_t, Nat.mod_self]
          simp only [d, hgap_rw, h1, Nat.sub_zero, Nat.add_mod_right,
            Nat.mod_eq_of_lt (idx ⟨0, hmTot_pos⟩).isLt]
          omega
      by_cases hwrap2 : (idx t).val + 1 + s < M
      · have hrcur_eq : rcur.val = (idx t).val + 1 + s := by
          rw [hrcur_val, Nat.mod_eq_of_lt hwrap2]
        have hgt : idx t < idx tcur := by rw [hcur_eq]; change (idx t).val < rcur.val; omega
        have htgt : t < tcur := hidx_mono.lt_iff_lt.mp hgt
        change t.val < tcur.val at htgt
        have := tcur.isLt; omega
      · have hrcur_eq : rcur.val = (idx t).val + 1 + s - M := by
          rw [hrcur_val, Nat.mod_eq_sub_mod (by omega),
            Nat.mod_eq_of_lt (by have := (idx ⟨0, hmTot_pos⟩).isLt; omega)]
        have hlt0 : idx tcur < idx ⟨0, hmTot_pos⟩ := by
          rw [hcur_eq]; change rcur.val < (idx ⟨0, hmTot_pos⟩).val; omega
        have htlt : tcur < ⟨0, hmTot_pos⟩ := hidx_mono.lt_iff_lt.mp hlt0
        change tcur.val < 0 at htlt
        omega
  have hflip : ∀ t : Fin mTot, (proj (w (idx t))).isLeft ≠ (proj (w (idx (t + 1)))).isLeft := by
    intro t
    rw [← hbetween t]
    rcases horig_sides _ _ (hw_adj (idx t)) (hidx_mem t) with
      ⟨_, _, h1, h2, _, _⟩ | ⟨_, _, h1, h2, _, _⟩ <;> simp [h1, h2]
  have hparity_alt : ∀ t : Fin mTot,
      (proj (w (idx t))).isLeft = xor (proj (w (idx ⟨0, hmTot_pos⟩))).isLeft (t.val % 2 = 1) := by
    intro t
    rcases t with ⟨t, ht⟩
    induction t with
    | zero => simp
    | succ t ih =>
      have h1 := hflip ⟨t, by omega⟩
      have hsucc : (⟨t, by omega⟩ : Fin mTot) + 1 = ⟨t + 1, ht⟩ := by
        apply Fin.ext; simp only [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < mTot), Nat.mod_eq_of_lt ht]
      rw [hsucc] at h1
      have h2 := ih (by omega)
      rw [h2] at h1
      have hm2 : t % 2 = 0 ∨ t % 2 = 1 := by omega
      cases h0 : (proj (w (idx ⟨0, hmTot_pos⟩))).isLeft <;>
      cases hc : (proj (w (idx ⟨t + 1, ht⟩))).isLeft <;>
      rcases hm2 with hm | hm
      all_goals rw [h0, hc] at h1
      all_goals simp only [hm, show (t + 1) % 2 = (t % 2 + 1) % 2 by omega] at h1 ⊢
      all_goals try exact absurd rfl h1
      all_goals try rfl
      all_goals simp at h1 ⊢
  have hm_even : mTot % 2 = 0 := by
    have hlast := hflip ⟨mTot - 1, by omega⟩
    have hsucc : (⟨mTot - 1, by omega⟩ : Fin mTot) + 1 = ⟨0, hmTot_pos⟩ := by
      apply Fin.ext; simp only [Fin.val_add, Fin.val_one']
      by_cases hm2 : 1 < mTot
      · rw [Nat.mod_eq_of_lt hm2, show mTot - 1 + 1 = mTot by omega, Nat.mod_self]
      · have hm1 : mTot = 1 := by omega
        simp [hm1]
    rw [hsucc, hparity_alt ⟨mTot - 1, by omega⟩] at hlast
    have hm2 : mTot % 2 = 0 ∨ mTot % 2 = 1 := by omega
    rcases hm2 with h | h
    · exact h
    · exfalso
      have hodd : (mTot - 1) % 2 = 0 := by omega
      have hv : (⟨mTot - 1, by omega⟩ : Fin mTot).val = mTot - 1 := rfl
      rw [hv, hodd] at hlast
      cases h0 : (proj (w (idx ⟨0, hmTot_pos⟩))).isLeft <;>
        (rw [h0] at hlast; simp only [show ¬ (0 = 1) by decide, decide_false, Bool.xor_false, ne_eq, not_true_eq_false] at hlast)
  let r := mTot / 2 - 1
  have h2r : 2 * (r + 1) = mTot := by omega
  have hr_le : r + 1 ≤ a + 2 := by omega
  let shift : Fin mTot := if (proj (w (idx ⟨0, hmTot_pos⟩))).isLeft then ⟨0, hmTot_pos⟩ else ⟨1, by omega⟩
  have hshift_left : ∀ s : Fin (r + 1), (proj (w (idx (shift + ⟨2 * s.val, by omega⟩)))).isLeft = true := by
    intro s
    have hval : (shift + ⟨2 * s.val, by omega⟩).val % 2 = if (proj (w (idx ⟨0, hmTot_pos⟩))).isLeft then 0 else 1 := by
      dsimp only [shift]
      split_ifs with h0
      · simp only [Fin.val_add, zero_add, Nat.mod_eq_of_lt (by omega : 2 * s.val < mTot)]; omega
      · simp only [Fin.val_add]
        rw [Nat.mod_eq_of_lt (by omega : 1 + 2 * s.val < mTot)]; omega
    rw [hparity_alt]
    cases h0 : (proj (w (idx ⟨0, hmTot_pos⟩))).isLeft
    · rw [h0] at hval; simp only [Bool.false_eq_true, ↓reduceIte] at hval; rw [hval]; decide
    · rw [h0] at hval; simp only [↓reduceIte] at hval; rw [hval]; decide
  have hshift_right : ∀ s : Fin (r + 1), (proj (w (idx (shift + ⟨2 * s.val + 1, by omega⟩)))).isLeft = false := by
    intro s
    have h1 := hflip (shift + ⟨2 * s.val, by omega⟩)
    have hstep : shift + ⟨2 * s.val, by omega⟩ + 1 = shift + ⟨2 * s.val + 1, by omega⟩ := by
      rw [add_assoc]; congr 1
      apply Fin.ext; simp only [Fin.val_add, Fin.val_one']
      rw [Nat.mod_eq_of_lt (by omega : 1 < mTot), Nat.mod_eq_of_lt (by omega : 2 * s.val + 1 < mTot)]
    rw [hstep, hshift_left s] at h1
    cases hc : (proj (w (idx (shift + ⟨2 * s.val + 1, by omega⟩)))).isLeft
    · rfl
    · rw [hc] at h1; exact absurd rfl h1
  let getL : Fin (q₀ + 1) ⊕ Fin q₀ → Fin (q₀ + 1) := fun z => match z with | Sum.inl u => u | Sum.inr _ => ⟨0, Nat.succ_pos q₀⟩
  let getR : Fin (q₀ + 1) ⊕ Fin q₀ → Fin q₀ := fun z => match z with | Sum.inr v => v | Sum.inl _ => ⟨0, by
    rcases horig_sides _ _ (hw_adj (idx ⟨0, hmTot_pos⟩)) (hidx_mem ⟨0, hmTot_pos⟩) with ⟨_, v, _, _, _, _⟩ | ⟨_, v, _, _, _, _⟩
    · exact Nat.pos_of_ne_zero (fun h => by rw [h] at v; exact Fin.elim0 v)
    · exact Nat.pos_of_ne_zero (fun h => by rw [h] at v; exact Fin.elim0 v)⟩
  let uT : Fin (r + 1) → Fin (q₀ + 1) := fun s => getL (proj (w (idx (shift + ⟨2 * s.val, by omega⟩))))
  let vT : Fin (r + 1) → Fin q₀ := fun s => getR (proj (w (idx (shift + ⟨2 * s.val + 1, by omega⟩))))
  have huT_eq : ∀ s : Fin (r + 1), proj (w (idx (shift + ⟨2 * s.val, by omega⟩))) = Sum.inl (uT s) := by
    intro s
    have hl := hshift_left s
    cases hp : proj (w (idx (shift + ⟨2 * s.val, by omega⟩))) with
    | inl u => simp [uT, getL, hp]
    | inr v => simp [hp] at hl
  have hvT_eq : ∀ s : Fin (r + 1), proj (w (idx (shift + ⟨2 * s.val + 1, by omega⟩))) = Sum.inr (vT s) := by
    intro s
    have hr := hshift_right s
    cases hp : proj (w (idx (shift + ⟨2 * s.val + 1, by omega⟩))) with
    | inl u => simp [hp] at hr
    | inr v => simp [vT, getR, hp]
  have hstep1 : ∀ s : Fin (r + 1), (shift + ⟨2 * s.val, by omega⟩) + 1 = shift + ⟨2 * s.val + 1, by omega⟩ := by
    intro s; rw [add_assoc]; congr 1
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_one']
    have h1lt : 1 % mTot = 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1lt, Nat.mod_eq_of_lt (by omega : 2 * s.val + 1 < mTot)]
  have hstep2 : ∀ s : Fin (r + 1), (shift + ⟨2 * s.val + 1, by omega⟩) + 1 = shift + ⟨2 * (s + 1).val, by have := (s + 1).isLt; omega⟩ := by
    intro s; rw [add_assoc]; congr 1
    apply Fin.ext
    simp only [Fin.val_add, Fin.val_one']
    have h1lt : 1 % mTot = 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1lt]
    by_cases hlt : s.val + 1 < r + 1
    · rw [Nat.mod_eq_of_lt (by omega : 1 < r + 1), Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega : 2 * s.val + 1 + 1 < mTot)]
      omega
    · have hs1 : s.val + 1 = r + 1 := by omega
      have h1r : (s.val + 1 % (r + 1)) % (r + 1) = 0 := by
        by_cases hr2 : 1 < r + 1
        · rw [Nat.mod_eq_of_lt hr2, hs1, Nat.mod_self]
        · have hr0 : r = 0 := by omega
          have hs0 : s.val = 0 := by omega
          simp [hr0, hs0]
      rw [h1r, mul_zero, show 2 * s.val + 1 + 1 = mTot by omega, Nat.mod_self]
  have hadjT : ∀ s : Fin (r + 1), vT s ∈ G₀ (uT s) ∧ vT s ∈ G₀ (uT (s + 1)) := by
    intro s
    constructor
    · let t0 : Fin mTot := shift + ⟨2 * s.val, by omega⟩
      have h1 := hbetween t0
      have hst1 : t0 + 1 = shift + ⟨2 * s.val + 1, by omega⟩ := hstep1 s
      rw [hst1, hvT_eq s] at h1
      rcases horig_sides _ _ (hw_adj (idx t0)) (hidx_mem t0) with ⟨u, v, hu, hv, huv, _⟩ | ⟨_, _, h1', _, _, _⟩
      · have hu' : proj (w (idx t0)) = Sum.inl (uT s) := huT_eq s
        rw [hu'] at hu; rw [h1] at hv
        cases hu; cases hv; exact huv
      · have hu' : proj (w (idx t0)) = Sum.inl (uT s) := huT_eq s
        rw [hu'] at h1'; cases h1'
    · let t1 : Fin mTot := shift + ⟨2 * s.val + 1, by omega⟩
      have h2 := hbetween t1
      have hst2 : t1 + 1 = shift + ⟨2 * (s + 1).val, by have := (s + 1).isLt; omega⟩ := hstep2 s
      rw [hst2, huT_eq (s + 1)] at h2
      rcases horig_sides _ _ (hw_adj (idx t1)) (hidx_mem t1) with ⟨_, _, h1', _, _, _⟩ | ⟨u, v, hv, hu, huv, _⟩
      · have hv' : proj (w (idx t1)) = Sum.inr (vT s) := hvT_eq s
        rw [hv'] at h1'; cases h1'
      · have hv' : proj (w (idx t1)) = Sum.inr (vT s) := hvT_eq s
        rw [hv'] at hv; rw [h2] at hu
        cases hu; cases hv; exact huv
  have hne1T : ∀ i j : Fin (r + 1), i ≠ j → ¬ (uT i = uT j ∧ vT i = vT j) := by
    intro i j hij ⟨hu, hv⟩
    have hset : ({proj (w (idx (shift + ⟨2 * i.val, by omega⟩))),
        proj (w (idx (shift + ⟨2 * i.val, by omega⟩) + 1))} : Finset _) =
        {proj (w (idx (shift + ⟨2 * j.val, by omega⟩))),
        proj (w (idx (shift + ⟨2 * j.val, by omega⟩) + 1))} := by
      rw [hbetween, hbetween, hstep1, hstep1, huT_eq, huT_eq, hvT_eq, hvT_eq, hu, hv]
    have heq := horig_unique _ _ (hidx_mem _) (hidx_mem _) hset
    have hteq : shift + ⟨2 * i.val, by omega⟩ = shift + ⟨2 * j.val, by omega⟩ := hidx_mono.injective heq
    have h2eq := add_left_cancel hteq
    have hv' := congrArg Fin.val h2eq; dsimp at hv'
    exact hij (Fin.ext (by omega))
  have hne2T : ∀ i j : Fin (r + 1), i ≠ j → ¬ (uT (i + 1) = uT (j + 1) ∧ vT i = vT j) := by
    intro i j hij ⟨hu, hv⟩
    have hset : ({proj (w (idx (shift + ⟨2 * i.val + 1, by omega⟩))),
        proj (w (idx (shift + ⟨2 * i.val + 1, by omega⟩) + 1))} : Finset _) =
        {proj (w (idx (shift + ⟨2 * j.val + 1, by omega⟩))),
        proj (w (idx (shift + ⟨2 * j.val + 1, by omega⟩) + 1))} := by
      rw [hbetween, hbetween, hstep2, hstep2, huT_eq, huT_eq, hvT_eq, hvT_eq, hu, hv]
    have heq := horig_unique _ _ (hidx_mem _) (hidx_mem _) hset
    have hteq : shift + ⟨2 * i.val + 1, by omega⟩ = shift + ⟨2 * j.val + 1, by omega⟩ := hidx_mono.injective heq
    have h2eq := add_left_cancel hteq
    have hv' := congrArg Fin.val h2eq; dsimp at hv'
    exact hij (Fin.ext (by omega))
  have hne3T : ∀ i j : Fin (r + 1), ¬ (uT i = uT (j + 1) ∧ vT i = vT j) := by
    intro i j ⟨hu, hv⟩
    have hset : ({proj (w (idx (shift + ⟨2 * i.val, by omega⟩))),
        proj (w (idx (shift + ⟨2 * i.val, by omega⟩) + 1))} : Finset _) =
        {proj (w (idx (shift + ⟨2 * j.val + 1, by omega⟩))),
        proj (w (idx (shift + ⟨2 * j.val + 1, by omega⟩) + 1))} := by
      rw [hbetween, hbetween, hstep1, hstep2, huT_eq, huT_eq, hvT_eq, hvT_eq, hu, hv, Finset.pair_comm]
    have heq := horig_unique _ _ (hidx_mem _) (hidx_mem _) hset
    have hteq : shift + ⟨2 * i.val, by omega⟩ = shift + ⟨2 * j.val + 1, by omega⟩ := hidx_mono.injective heq
    have h2eq := add_left_cancel hteq
    have hv' := congrArg Fin.val h2eq; dsimp at hv'
    omega
  rcases closed_trail_has_cycle G₀ r uT vT hadjT hne1T hne2T hne3T with ⟨a₀, us₀, vs₀, hale, hcyc₀⟩
  exact ⟨a₀, us₀, vs₀, le_trans hale hr_le, hcyc₀⟩

noncomputable def sigma1 : GenEdge (G1 G₀) → LinEq (GEdge G₀) := fun e =>
  match e.1 with
  | (Sum.inl ⟨u, j⟩, Sum.inl _) => ({portEdgeL G₀ u j}, false)
  | (Sum.inl ⟨u, j⟩, Sum.inr ⟨_, t⟩) =>
      if j.val = t.val then (prefSet (portEdgeL G₀ u) t.val, true)
      else (prefSet (portEdgeL G₀ u) t.val, false)
  | (Sum.inr ⟨v, t⟩, Sum.inl ⟨_, j⟩) =>
      if j.val = t.val then (prefSet (portEdgeR G₀ v) t.val, true)
      else (prefSet (portEdgeR G₀ v) t.val, false)
  | (Sum.inr _, Sum.inr _) => (∅, false)

lemma subcubic_sim (hL2 : ∀ u, 2 ≤ (G₀ u).card) (hR2 : ∀ v, 2 ≤ (rightNbrs G₀ v).card)
    (hL16 : ∀ u, (G₀ u).card ≤ 16) (hR16 : ∀ v, (rightNbrs G₀ v).card ≤ 16)
    (k : ℕ) (hk : 1 ≤ k) (π₁ : List (LinKLine (GenEdge (G1 G₀))))
    (hπ₁ : IsLinKRefutation k (genGraphPHP (G1 G₀)) π₁) :
    ∃ π₀ : List (LinKLine (GEdge G₀)),
      IsLinKRefutation k (funGraphPHP G₀) π₀ ∧ π₀.length ≤ 1 + 1200 * π₁.length := by
  classical
  let u0 : Fin (q₀ + 1) := ⟨0, Nat.succ_pos q₀⟩
  let A₀ : Clause (GEdge G₀) :=
    Finset.univ.filter (fun l : Literal (GEdge G₀) => l.1.1.1 = u0 ∧ l.2 = true)
  have hA₀ : A₀ ∈ funGraphPHP G₀ := Or.inl (Or.inl ⟨u0, rfl⟩)
  have hamoL : ∀ u (a b : Fin (degL G₀ u)), a ≠ b →
      ({(portEdgeL G₀ u a, false), (portEdgeL G₀ u b, false)} : Clause (GEdge G₀)) ∈ funGraphPHP G₀ := by
    intro u a b hab
    refine Or.inr ⟨portEdgeL G₀ u a, portEdgeL G₀ u b, rfl, ?_, rfl⟩
    intro h; exact hab ((enumL G₀ u).injective (Subtype.ext h))
  have hamoR : ∀ v (a b : Fin (degR G₀ v)), a ≠ b →
      ({(portEdgeR G₀ v a, false), (portEdgeR G₀ v b, false)} : Clause (GEdge G₀)) ∈ funGraphPHP G₀ := by
    intro v a b hab
    refine Or.inl (Or.inr ⟨portEdgeR G₀ v a, portEdgeR G₀ v b, rfl, ?_, rfl⟩)
    intro h; exact hab ((enumR G₀ v).injective (Subtype.ext h))
  have haloL : ∀ u, Finset.univ.image (fun i : Fin (degL G₀ u) => (portEdgeL G₀ u i, true)) ∈ funGraphPHP G₀ := by
    intro u
    refine Or.inl (Or.inl ⟨u, ?_⟩)
    ext ⟨e, b⟩
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, Prod.mk.injEq]
    constructor
    · rintro ⟨i, rfl, rfl⟩; exact ⟨rfl, rfl⟩
    · rintro ⟨heu, rfl⟩
      rcases e with ⟨⟨u', v'⟩, hv'⟩
      dsimp at heu; subst heu
      refine ⟨(enumL G₀ u').symm ⟨v', hv'⟩, ?_, rfl⟩
      apply Subtype.ext; simp [portEdgeL]
  have hax : ∀ C ∈ genGraphPHP (G1 G₀), ∀ π₀,
      IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' funGraphPHP G₀) π₀ →
      linKOfClause A₀ ∈ π₀ →
      ∃ π', IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' funGraphPHP G₀) π' ∧
        (∀ L ∈ π₀, L ∈ π') ∧ substLine (sigma1 G₀) (linKOfClause C) ∈ π' ∧
        π'.length ≤ π₀.length + 1200 := by
    intro C hC π₀ hder hA0in
    have hM1 : ∀ S ∈ substLine (sigma1 G₀) (linKOfClause C), S.card = 1 :=
      substLine_clause_card_one (sigma1 G₀) C
    have hM_taut : (∀ a : GEdge G₀ → Bool, LinKLineSat a (substLine (sigma1 G₀) (linKOfClause C))) →
        ∃ π', IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' funGraphPHP G₀) π' ∧
          (∀ L ∈ π₀, L ∈ π') ∧ substLine (sigma1 G₀) (linKOfClause C) ∈ π' ∧
          π'.length ≤ π₀.length + 1200 := by
      intro htaut
      have hw := isLinKWeakening_one_sem (L := linKOfClause A₀) hM1 (fun a _ => htaut a)
      have hd1 := IsLinKDerivation.weak hder hA0in hw (fun T hT => by rw [hM1 T hT]; exact hk)
      exact ⟨_ :: π₀, hd1, fun L hL => by simp [hL], by simp, by simp⟩
    have hM_from_amoL : ∀ u (j : Fin (degL G₀ u)) (hj : 0 < j.val),
        (∀ a : GEdge G₀ → Bool,
          (parity a (prefSet (portEdgeL G₀ u) (j.val - 1)) = false ∨ a (portEdgeL G₀ u j) = false) →
          LinKLineSat a (substLine (sigma1 G₀) (linKOfClause C))) →
        ∃ π', IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' funGraphPHP G₀) π' ∧
          (∀ L ∈ π₀, L ∈ π') ∧ substLine (sigma1 G₀) (linKOfClause C) ∈ π' ∧
          π'.length ≤ π₀.length + 1200 := by
      intro u j hj himp
      rcases derive_amo_prefix hk (funGraphPHP G₀) (portEdgeL_inj G₀ u) (hamoL u) j (j.val - 1)
        (by omega) π₀ hder with ⟨π₁, hder1, hsub1, hL1, hlen1⟩
      have hw : IsLinKWeakening {{(prefSet (portEdgeL G₀ u) (j.val - 1), false)}, {({portEdgeL G₀ u j}, false)}}
          (substLine (sigma1 G₀) (linKOfClause C)) := by
        apply isLinKWeakening_one_sem hM1
        intro a hsat
        apply himp a
        rcases hsat with ⟨T, hT, hTsat⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hT
        rcases hT with rfl | rfl
        · left; have := hTsat _ (Finset.mem_singleton_self _); rwa [linEqSat_iff_parity] at this
        · right; have := hTsat _ (Finset.mem_singleton_self _); rwa [linEqSat_iff_parity, parity_singleton] at this
      have hd2 := IsLinKDerivation.weak hder1 hL1 hw (fun T hT => by rw [hM1 T hT]; exact hk)
      have hj16 : j.val ≤ 16 := le_trans (le_of_lt j.isLt) (hL16 u)
      refine ⟨_ :: π₁, hd2, fun L hL => by simp [hsub1 L hL], by simp, ?_⟩
      simp only [List.length_cons]; omega
    have hM_from_amoR : ∀ v (j : Fin (degR G₀ v)) (hj : 0 < j.val),
        (∀ a : GEdge G₀ → Bool,
          (parity a (prefSet (portEdgeR G₀ v) (j.val - 1)) = false ∨ a (portEdgeR G₀ v j) = false) →
          LinKLineSat a (substLine (sigma1 G₀) (linKOfClause C))) →
        ∃ π', IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' funGraphPHP G₀) π' ∧
          (∀ L ∈ π₀, L ∈ π') ∧ substLine (sigma1 G₀) (linKOfClause C) ∈ π' ∧
          π'.length ≤ π₀.length + 1200 := by
      intro v j hj himp
      rcases derive_amo_prefix hk (funGraphPHP G₀) (portEdgeR_inj G₀ v) (hamoR v) j (j.val - 1)
        (by omega) π₀ hder with ⟨π₁, hder1, hsub1, hL1, hlen1⟩
      have hw : IsLinKWeakening {{(prefSet (portEdgeR G₀ v) (j.val - 1), false)}, {({portEdgeR G₀ v j}, false)}}
          (substLine (sigma1 G₀) (linKOfClause C)) := by
        apply isLinKWeakening_one_sem hM1
        intro a hsat
        apply himp a
        rcases hsat with ⟨T, hT, hTsat⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hT
        rcases hT with rfl | rfl
        · left; have := hTsat _ (Finset.mem_singleton_self _); rwa [linEqSat_iff_parity] at this
        · right; have := hTsat _ (Finset.mem_singleton_self _); rwa [linEqSat_iff_parity, parity_singleton] at this
      have hd2 := IsLinKDerivation.weak hder1 hL1 hw (fun T hT => by rw [hM1 T hT]; exact hk)
      have hj16 : j.val ≤ 16 := le_trans (le_of_lt j.isLt) (hR16 v)
      refine ⟨_ :: π₁, hd2, fun L hL => by simp [hsub1 L hL], by simp, ?_⟩
      simp only [List.length_cons]; omega
    have hsat_iff : ∀ a, LinKLineSat a (substLine (sigma1 G₀) (linKOfClause C)) ↔
        ∃ l ∈ C, substAssign (sigma1 G₀) a l.1 = l.2 := by
      intro a; rw [substLine_sat, linKOfClause_sat_iff]
    rcases hC with (⟨x, rfl⟩ | ⟨e1, e2, he2, hne1, rfl⟩) | ⟨e1, e2, he1, hne2, rfl⟩
    · rcases x with ⟨u, j⟩ | ⟨v, t⟩
      · have hdu2 : 2 ≤ degL G₀ u := hL2 u
        by_cases hj0 : j.val = 0
        · apply hM_taut; intro a; rw [hsat_iff]
          let v0 := (enumL G₀ u j).1
          let j0' := (enumR G₀ v0).symm ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (enumL G₀ u j).2⟩⟩
          let eOrig : GenEdge (G1 G₀) := ⟨(Sum.inl ⟨u, j⟩, Sum.inl ⟨v0, j0'⟩),
            (mem_G1_iff G₀ _ _).mpr ⟨rfl, by simp [j0', v0]⟩⟩
          let eSp : GenEdge (G1 G₀) := ⟨(Sum.inl ⟨u, j⟩, Sum.inr ⟨u, ⟨0, by omega⟩⟩),
            (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inl hj0⟩⟩
          cases ha : a (portEdgeL G₀ u j)
          · refine ⟨(eSp, true), by simp [eSp], ?_⟩
            have hj_eq : j = ⟨0, by omega⟩ := Fin.ext hj0
            simp only [substAssign, sigma1, eSp, hj0, ↓reduceIte, prefSet_zero (by omega) (portEdgeL G₀ u),
              parity_singleton, ← hj_eq, ha]; rfl
          · refine ⟨(eOrig, true), by simp [eOrig], ?_⟩
            simp only [substAssign, sigma1, eOrig, parity_singleton, Bool.xor_false, ha]
        · by_cases hjlast : j.val < degL G₀ u - 1
          · apply hM_taut; intro a; rw [hsat_iff]
            let v0 := (enumL G₀ u j).1
            let j0' := (enumR G₀ v0).symm ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (enumL G₀ u j).2⟩⟩
            let eOrig : GenEdge (G1 G₀) := ⟨(Sum.inl ⟨u, j⟩, Sum.inl ⟨v0, j0'⟩),
              (mem_G1_iff G₀ _ _).mpr ⟨rfl, by simp [j0', v0]⟩⟩
            let ePrev : GenEdge (G1 G₀) := ⟨(Sum.inl ⟨u, j⟩, Sum.inr ⟨u, ⟨j.val - 1, by omega⟩⟩),
              (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inr (by (try dsimp); omega)⟩⟩
            let eNext : GenEdge (G1 G₀) := ⟨(Sum.inl ⟨u, j⟩, Sum.inr ⟨u, ⟨j.val, hjlast⟩⟩),
              (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inl rfl⟩⟩
            cases ha : a (portEdgeL G₀ u j)
            · cases hp : parity a (prefSet (portEdgeL G₀ u) (j.val - 1))
              · refine ⟨(eNext, true), by simp [eNext], ?_⟩
                simp only [substAssign, sigma1, eNext, ↓reduceIte]
                have hjs : j.val = (j.val - 1) + 1 := by omega
                have hjeq : (⟨(j.val - 1) + 1, by omega⟩ : Fin (degL G₀ u)) = j := Fin.ext (by (try dsimp); omega)
                rw [hjs, prefSet_succ (portEdgeL G₀ u) (j.val - 1) (by omega),
                  parity_insert a _ _ (not_mem_prefSet (portEdgeL_inj G₀ u) (j.val - 1) (by omega)),
                  hjeq, ha, hp]; rfl
              · refine ⟨(ePrev, true), by simp [ePrev], ?_⟩
                simp only [substAssign, sigma1, ePrev, show ¬ (j.val = j.val - 1) by omega, ↓reduceIte,
                  Bool.xor_false, hp]
            · refine ⟨(eOrig, true), by simp [eOrig], ?_⟩
              simp only [substAssign, sigma1, eOrig, parity_singleton, Bool.xor_false, ha]
          · have hjeq : j = ⟨degL G₀ u - 1, by omega⟩ := Fin.ext (by dsimp; have := j.isLt; omega)
            rcases derive_alo_prefix hk hdu2 (funGraphPHP G₀) (portEdgeL_inj G₀ u) (hamoL u) (haloL u)
              (degL G₀ u - 2) (by omega) π₀ hder with ⟨π₁, hder1, hsub1, hL1, hlen1⟩
            have hd2 := IsLinKDerivation.weak hder1 hL1 (by
              apply isLinKWeakening_one_sem hM1
              intro a hsat
              rw [hsat_iff]
              let v0 := (enumL G₀ u j).1
              let j0' := (enumR G₀ v0).symm ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (enumL G₀ u j).2⟩⟩
              let eOrig : GenEdge (G1 G₀) := ⟨(Sum.inl ⟨u, j⟩, Sum.inl ⟨v0, j0'⟩),
                (mem_G1_iff G₀ _ _).mpr ⟨rfl, by simp [j0', v0]⟩⟩
              let ePrev : GenEdge (G1 G₀) := ⟨(Sum.inl ⟨u, j⟩, Sum.inr ⟨u, ⟨j.val - 1, by omega⟩⟩),
                (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inr (by (try dsimp); omega)⟩⟩
              rcases hsat with ⟨T, hT, hTsat⟩
              simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hT
              rcases hT with rfl | ⟨i, hi, rfl⟩
              · have hp : parity a (prefSet (portEdgeL G₀ u) (degL G₀ u - 2)) = true := by
                  have := hTsat _ (Finset.mem_singleton_self _)
                  rwa [linEqSat_iff_parity] at this
                refine ⟨(ePrev, true), by simp [ePrev], ?_⟩
                have hjm : j.val - 1 = degL G₀ u - 2 := by rw [hjeq]; dsimp; omega
                simp only [substAssign, sigma1, ePrev, show ¬ (j.val = j.val - 1) by omega, ↓reduceIte, Bool.xor_false]; rw [hjm, hp]
              · have hij : i = j := by
                  apply Fin.ext; rw [hjeq]; dsimp; have := i.isLt; omega
                subst hij
                have ha : a (portEdgeL G₀ u i) = true := by
                  have := hTsat _ (Finset.mem_singleton_self _)
                  rwa [linEqSat_iff_parity, parity_singleton] at this
                refine ⟨(eOrig, true), by simp [eOrig], ?_⟩
                simp only [substAssign, sigma1, eOrig, parity_singleton, Bool.xor_false, ha])
              (fun T hT => by rw [hM1 T hT]; exact hk)
            have hd16 : degL G₀ u ≤ 16 := hL16 u
            refine ⟨_ :: π₁, hd2, fun L hL => by simp [hsub1 L hL], by simp, ?_⟩
            simp only [List.length_cons]
            have hmul : (4 * degL G₀ u + 5) * (degL G₀ u - 2 + 1) ≤ 1190 := by
              have h1 : 4 * degL G₀ u + 5 ≤ 69 := by omega
              have h2 : degL G₀ u - 2 + 1 ≤ 15 := by omega
              nlinarith
            omega
      · apply hM_taut; intro a; rw [hsat_iff]
        let eL0 : GenEdge (G1 G₀) := ⟨(Sum.inr ⟨v, t⟩, Sum.inl ⟨v, ⟨t.val, by omega⟩⟩),
          (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inl rfl⟩⟩
        let eR0 : GenEdge (G1 G₀) := ⟨(Sum.inr ⟨v, t⟩, Sum.inl ⟨v, ⟨t.val + 1, by omega⟩⟩),
          (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inr rfl⟩⟩
        cases hp : parity a (prefSet (portEdgeR G₀ v) t.val)
        · refine ⟨(eL0, true), by simp [eL0], ?_⟩
          simp only [substAssign, sigma1, eL0, ↓reduceIte, hp]; rfl
        · refine ⟨(eR0, true), by simp [eR0], ?_⟩
          simp only [substAssign, sigma1, eR0, show ¬ (t.val + 1 = t.val) by omega, ↓reduceIte,
            Bool.xor_false, hp]
    · rcases e1 with ⟨⟨x1, y1⟩, h1⟩; rcases e2 with ⟨⟨x2, y2⟩, h2⟩
      dsimp at he2 hne1; subst he2
      rw [mem_G1_iff] at h1 h2
      rcases y1 with ⟨v, j⟩ | ⟨u, t⟩
      · rcases x1 with ⟨u1, j1⟩ | ⟨v1, t1⟩ <;> rcases x2 with ⟨u2, j2⟩ | ⟨v2, t2⟩
        all_goals simp only [adj1Prop] at h1 h2
        · exfalso; apply hne1; congr 1
          rcases h1 with ⟨hv1, hu1⟩; rcases h2 with ⟨hv2, hu2⟩
          have hu12 : u1 = u2 := hu1.symm.trans hu2
          subst hu12
          refine Sigma.ext rfl (heq_of_eq ?_)
          exact (enumL G₀ u1).injective (Subtype.ext (hv1.trans hv2.symm))
        · rcases h2 with ⟨rfl, hjt | hjt⟩
          · by_cases hj0 : j.val = 0
            · apply hM_taut; intro a; rw [hsat_iff]
              have ht0 : t2.val = 0 := by omega
              have hj_eq : j = ⟨0, by omega⟩ := Fin.ext hj0
              have he12 : portEdgeL G₀ u1 j1 = portEdgeR G₀ v j := by
                apply Subtype.ext; simp [portEdgeL, portEdgeR, h1.1, h1.2]
              cases ha : a (portEdgeR G₀ v j)
              · refine ⟨(⟨(Sum.inl ⟨u1, j1⟩, Sum.inl ⟨v, j⟩), (mem_G1_iff G₀ _ _).mpr h1⟩, false), by simp, ?_⟩
                simp only [substAssign, sigma1, parity_singleton, Bool.xor_false, he12, ha]
              · refine ⟨(⟨(Sum.inr ⟨v, t2⟩, Sum.inl ⟨v, j⟩), (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inl hjt⟩⟩, false), by simp, ?_⟩
                simp only [substAssign, sigma1, hjt, ↓reduceIte, ht0, prefSet_zero (by omega) (portEdgeR G₀ v),
                  parity_singleton, ← hj_eq, ha]; rfl
            · apply hM_from_amoR v j (by omega); intro a hdisj; rw [hsat_iff]
              have he12 : portEdgeL G₀ u1 j1 = portEdgeR G₀ v j := by
                apply Subtype.ext; simp [portEdgeL, portEdgeR, h1.1, h1.2]
              rcases hdisj with hp | ha
              · cases ha' : a (portEdgeR G₀ v j)
                · refine ⟨(⟨(Sum.inl ⟨u1, j1⟩, Sum.inl ⟨v, j⟩), (mem_G1_iff G₀ _ _).mpr h1⟩, false), by simp, ?_⟩
                  simp only [substAssign, sigma1, parity_singleton, Bool.xor_false, he12, ha']
                · refine ⟨(⟨(Sum.inr ⟨v, t2⟩, Sum.inl ⟨v, j⟩), (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inl hjt⟩⟩, false), by simp, ?_⟩
                  simp only [substAssign, sigma1, hjt, ↓reduceIte]
                  have hts : t2.val = (j.val - 1) + 1 := by omega
                  have hjeq : (⟨(j.val - 1) + 1, by omega⟩ : Fin (degR G₀ v)) = j := Fin.ext (by (try dsimp); omega)
                  rw [hts, prefSet_succ (portEdgeR G₀ v) (j.val - 1) (by omega),
                    parity_insert a _ _ (not_mem_prefSet (portEdgeR_inj G₀ v) (j.val - 1) (by omega)),
                    hjeq, ha', hp]; rfl
              · refine ⟨(⟨(Sum.inl ⟨u1, j1⟩, Sum.inl ⟨v, j⟩), (mem_G1_iff G₀ _ _).mpr h1⟩, false), by simp, ?_⟩
                simp only [substAssign, sigma1, parity_singleton, Bool.xor_false, he12, ha]
          · apply hM_from_amoR v j (by omega); intro a hdisj; rw [hsat_iff]
            have he12 : portEdgeL G₀ u1 j1 = portEdgeR G₀ v j := by
              apply Subtype.ext; simp [portEdgeL, portEdgeR, h1.1, h1.2]
            rcases hdisj with hp | ha
            · refine ⟨(⟨(Sum.inr ⟨v, t2⟩, Sum.inl ⟨v, j⟩), (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inr hjt⟩⟩, false), by simp, ?_⟩
              have ht_eq : t2.val = j.val - 1 := by omega
              simp only [substAssign, sigma1, show ¬ (j.val = t2.val) by omega, ↓reduceIte, Bool.xor_false]; rw [ht_eq, hp]
            · refine ⟨(⟨(Sum.inl ⟨u1, j1⟩, Sum.inl ⟨v, j⟩), (mem_G1_iff G₀ _ _).mpr h1⟩, false), by simp, ?_⟩
              simp only [substAssign, sigma1, parity_singleton, Bool.xor_false, he12, ha]
        · rcases h1 with ⟨rfl, hjt | hjt⟩
          · by_cases hj0 : j.val = 0
            · apply hM_taut; intro a; rw [hsat_iff]
              have ht0 : t1.val = 0 := by omega
              have hj_eq : j = ⟨0, by omega⟩ := Fin.ext hj0
              have he12 : portEdgeL G₀ u2 j2 = portEdgeR G₀ v j := by
                apply Subtype.ext; simp [portEdgeL, portEdgeR, h2.1, h2.2]
              cases ha : a (portEdgeR G₀ v j)
              · refine ⟨(⟨(Sum.inl ⟨u2, j2⟩, Sum.inl ⟨v, j⟩), (mem_G1_iff G₀ _ _).mpr h2⟩, false), by simp, ?_⟩
                simp only [substAssign, sigma1, parity_singleton, Bool.xor_false, he12, ha]
              · refine ⟨(⟨(Sum.inr ⟨v, t1⟩, Sum.inl ⟨v, j⟩), (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inl hjt⟩⟩, false), by simp, ?_⟩
                simp only [substAssign, sigma1, hjt, ↓reduceIte, ht0, prefSet_zero (by omega) (portEdgeR G₀ v),
                  parity_singleton, ← hj_eq, ha]; rfl
            · apply hM_from_amoR v j (by omega); intro a hdisj; rw [hsat_iff]
              have he12 : portEdgeL G₀ u2 j2 = portEdgeR G₀ v j := by
                apply Subtype.ext; simp [portEdgeL, portEdgeR, h2.1, h2.2]
              rcases hdisj with hp | ha
              · cases ha' : a (portEdgeR G₀ v j)
                · refine ⟨(⟨(Sum.inl ⟨u2, j2⟩, Sum.inl ⟨v, j⟩), (mem_G1_iff G₀ _ _).mpr h2⟩, false), by simp, ?_⟩
                  simp only [substAssign, sigma1, parity_singleton, Bool.xor_false, he12, ha']
                · refine ⟨(⟨(Sum.inr ⟨v, t1⟩, Sum.inl ⟨v, j⟩), (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inl hjt⟩⟩, false), by simp, ?_⟩
                  simp only [substAssign, sigma1, hjt, ↓reduceIte]
                  have hts : t1.val = (j.val - 1) + 1 := by omega
                  have hjeq : (⟨(j.val - 1) + 1, by omega⟩ : Fin (degR G₀ v)) = j := Fin.ext (by (try dsimp); omega)
                  rw [hts, prefSet_succ (portEdgeR G₀ v) (j.val - 1) (by omega),
                    parity_insert a _ _ (not_mem_prefSet (portEdgeR_inj G₀ v) (j.val - 1) (by omega)),
                    hjeq, ha', hp]; rfl
              · refine ⟨(⟨(Sum.inl ⟨u2, j2⟩, Sum.inl ⟨v, j⟩), (mem_G1_iff G₀ _ _).mpr h2⟩, false), by simp, ?_⟩
                simp only [substAssign, sigma1, parity_singleton, Bool.xor_false, he12, ha]
          · apply hM_from_amoR v j (by omega); intro a hdisj; rw [hsat_iff]
            have he12 : portEdgeL G₀ u2 j2 = portEdgeR G₀ v j := by
              apply Subtype.ext; simp [portEdgeL, portEdgeR, h2.1, h2.2]
            rcases hdisj with hp | ha
            · refine ⟨(⟨(Sum.inr ⟨v, t1⟩, Sum.inl ⟨v, j⟩), (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inr hjt⟩⟩, false), by simp, ?_⟩
              have ht_eq : t1.val = j.val - 1 := by omega
              simp only [substAssign, sigma1, show ¬ (j.val = t1.val) by omega, ↓reduceIte, Bool.xor_false]; rw [ht_eq, hp]
            · refine ⟨(⟨(Sum.inl ⟨u2, j2⟩, Sum.inl ⟨v, j⟩), (mem_G1_iff G₀ _ _).mpr h2⟩, false), by simp, ?_⟩
              simp only [substAssign, sigma1, parity_singleton, Bool.xor_false, he12, ha]
        · rcases h1 with ⟨rfl, hjt1 | hjt1⟩ <;> rcases h2 with ⟨rfl, hjt2 | hjt2⟩
          · exfalso; apply hne1; congr 2; exact Fin.ext (by (try dsimp); omega)
          · apply hM_from_amoR v j (by omega); intro a hdisj; rw [hsat_iff]
            rcases hdisj with hp | ha
            · refine ⟨(⟨(Sum.inr ⟨v, t2⟩, Sum.inl ⟨v, j⟩), (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inr hjt2⟩⟩, false), by simp, ?_⟩
              have ht2_eq : t2.val = j.val - 1 := by omega
              simp only [substAssign, sigma1, show ¬ (j.val = t2.val) by omega, ↓reduceIte, Bool.xor_false]; rw [ht2_eq, hp]
            · cases hp' : parity a (prefSet (portEdgeR G₀ v) (j.val - 1))
              · refine ⟨(⟨(Sum.inr ⟨v, t2⟩, Sum.inl ⟨v, j⟩), (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inr hjt2⟩⟩, false), by simp, ?_⟩
                have ht2_eq : t2.val = j.val - 1 := by omega
                simp only [substAssign, sigma1, show ¬ (j.val = t2.val) by omega, ↓reduceIte, Bool.xor_false]; rw [ht2_eq, hp']
              · refine ⟨(⟨(Sum.inr ⟨v, t1⟩, Sum.inl ⟨v, j⟩), (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inl hjt1⟩⟩, false), by simp, ?_⟩
                simp only [substAssign, sigma1, hjt1, ↓reduceIte]
                have hts : t1.val = (j.val - 1) + 1 := by omega
                have hjeq : (⟨(j.val - 1) + 1, by omega⟩ : Fin (degR G₀ v)) = j := Fin.ext (by (try dsimp); omega)
                rw [hts, prefSet_succ (portEdgeR G₀ v) (j.val - 1) (by omega),
                  parity_insert a _ _ (not_mem_prefSet (portEdgeR_inj G₀ v) (j.val - 1) (by omega)),
                  hjeq, ha, hp']; rfl
          · apply hM_from_amoR v j (by omega); intro a hdisj; rw [hsat_iff]
            rcases hdisj with hp | ha
            · refine ⟨(⟨(Sum.inr ⟨v, t1⟩, Sum.inl ⟨v, j⟩), (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inr hjt1⟩⟩, false), by simp, ?_⟩
              have ht1_eq : t1.val = j.val - 1 := by omega
              simp only [substAssign, sigma1, show ¬ (j.val = t1.val) by omega, ↓reduceIte, Bool.xor_false]; rw [ht1_eq, hp]
            · cases hp' : parity a (prefSet (portEdgeR G₀ v) (j.val - 1))
              · refine ⟨(⟨(Sum.inr ⟨v, t1⟩, Sum.inl ⟨v, j⟩), (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inr hjt1⟩⟩, false), by simp, ?_⟩
                have ht1_eq : t1.val = j.val - 1 := by omega
                simp only [substAssign, sigma1, show ¬ (j.val = t1.val) by omega, ↓reduceIte, Bool.xor_false]; rw [ht1_eq, hp']
              · refine ⟨(⟨(Sum.inr ⟨v, t2⟩, Sum.inl ⟨v, j⟩), (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inl hjt2⟩⟩, false), by simp, ?_⟩
                simp only [substAssign, sigma1, hjt2, ↓reduceIte]
                have hts : t2.val = (j.val - 1) + 1 := by omega
                have hjeq : (⟨(j.val - 1) + 1, by omega⟩ : Fin (degR G₀ v)) = j := Fin.ext (by (try dsimp); omega)
                rw [hts, prefSet_succ (portEdgeR G₀ v) (j.val - 1) (by omega),
                  parity_insert a _ _ (not_mem_prefSet (portEdgeR_inj G₀ v) (j.val - 1) (by omega)),
                  hjeq, ha, hp']; rfl
          · exfalso; apply hne1; congr 2; exact Fin.ext (by (try dsimp); omega)
      · rcases x1 with ⟨u1, j1⟩ | ⟨v1, t1⟩ <;> rcases x2 with ⟨u2, j2⟩ | ⟨v2, t2⟩
        all_goals simp only [adj1Prop] at h1 h2
        all_goals try exact False.elim h1
        all_goals try exact False.elim h2
        rcases h1 with ⟨rfl, h1 | h1⟩ <;> rcases h2 with ⟨rfl, h2 | h2⟩
        · exfalso; apply hne1; congr 2; exact Fin.ext (by omega)
        · apply hM_taut; intro a; rw [hsat_iff]
          cases hp : parity a (prefSet (portEdgeL G₀ u2) t.val)
          · refine ⟨(⟨(Sum.inl ⟨u2, j2⟩, Sum.inr ⟨u2, t⟩), (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inr h2⟩⟩, false), by simp, ?_⟩
            simp only [substAssign, sigma1, show ¬ (j2.val = t.val) by omega, ↓reduceIte, Bool.xor_false, hp]
          · refine ⟨(⟨(Sum.inl ⟨u2, j1⟩, Sum.inr ⟨u2, t⟩), (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inl h1⟩⟩, false), by simp, ?_⟩
            simp only [substAssign, sigma1, h1, ↓reduceIte, hp]; rfl
        · apply hM_taut; intro a; rw [hsat_iff]
          cases hp : parity a (prefSet (portEdgeL G₀ u2) t.val)
          · refine ⟨(⟨(Sum.inl ⟨u2, j1⟩, Sum.inr ⟨u2, t⟩), (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inr h1⟩⟩, false), by simp, ?_⟩
            simp only [substAssign, sigma1, show ¬ (j1.val = t.val) by omega, ↓reduceIte, Bool.xor_false, hp]
          · refine ⟨(⟨(Sum.inl ⟨u2, j2⟩, Sum.inr ⟨u2, t⟩), (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inl h2⟩⟩, false), by simp, ?_⟩
            simp only [substAssign, sigma1, h2, ↓reduceIte, hp]; rfl
        · exfalso; apply hne1; congr 2; exact Fin.ext (by omega)
    · rcases e1 with ⟨⟨x1, y1⟩, h1⟩; rcases e2 with ⟨⟨x2, y2⟩, h2⟩
      dsimp at he1 hne2; subst he1
      rw [mem_G1_iff] at h1 h2
      rcases x1 with ⟨u, j⟩ | ⟨v, t⟩
      · rcases y1 with ⟨v1, j1⟩ | ⟨u1, t1⟩ <;> rcases y2 with ⟨v2, j2⟩ | ⟨u2, t2⟩
        all_goals simp only [adj1Prop] at h1 h2
        · exfalso; apply hne2; congr 1
          rcases h1 with ⟨hv1, hu1⟩; rcases h2 with ⟨hv2, hu2⟩
          have hv12 : v1 = v2 := hv1.symm.trans hv2
          subst hv12
          refine Sigma.ext rfl (heq_of_eq ?_)
          exact (enumR G₀ v1).injective (Subtype.ext (hu1.trans hu2.symm))
        · rcases h2 with ⟨rfl, hjt | hjt⟩
          · by_cases hj0 : j.val = 0
            · apply hM_taut; intro a; rw [hsat_iff]
              have ht0 : t2.val = 0 := by omega
              have hj_eq : j = ⟨0, by omega⟩ := Fin.ext hj0
              cases ha : a (portEdgeL G₀ u j)
              · refine ⟨(⟨(Sum.inl ⟨u, j⟩, Sum.inl ⟨v1, j1⟩), (mem_G1_iff G₀ _ _).mpr h1⟩, false), by simp, ?_⟩
                simp only [substAssign, sigma1, parity_singleton, Bool.xor_false, ha]
              · refine ⟨(⟨(Sum.inl ⟨u, j⟩, Sum.inr ⟨u, t2⟩), (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inl hjt⟩⟩, false), by simp, ?_⟩
                simp only [substAssign, sigma1, hjt, ↓reduceIte, ht0, prefSet_zero (by omega) (portEdgeL G₀ u),
                  parity_singleton, ← hj_eq, ha]; rfl
            · apply hM_from_amoL u j (by omega); intro a hdisj; rw [hsat_iff]
              rcases hdisj with hp | ha
              · cases ha' : a (portEdgeL G₀ u j)
                · refine ⟨(⟨(Sum.inl ⟨u, j⟩, Sum.inl ⟨v1, j1⟩), (mem_G1_iff G₀ _ _).mpr h1⟩, false), by simp, ?_⟩
                  simp only [substAssign, sigma1, parity_singleton, Bool.xor_false, ha']
                · refine ⟨(⟨(Sum.inl ⟨u, j⟩, Sum.inr ⟨u, t2⟩), (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inl hjt⟩⟩, false), by simp, ?_⟩
                  simp only [substAssign, sigma1, hjt, ↓reduceIte]
                  have hts : t2.val = (j.val - 1) + 1 := by omega
                  have hjeq : (⟨(j.val - 1) + 1, by omega⟩ : Fin (degL G₀ u)) = j := Fin.ext (by (try dsimp); omega)
                  rw [hts, prefSet_succ (portEdgeL G₀ u) (j.val - 1) (by omega),
                    parity_insert a _ _ (not_mem_prefSet (portEdgeL_inj G₀ u) (j.val - 1) (by omega)),
                    hjeq, ha', hp]; rfl
              · refine ⟨(⟨(Sum.inl ⟨u, j⟩, Sum.inl ⟨v1, j1⟩), (mem_G1_iff G₀ _ _).mpr h1⟩, false), by simp, ?_⟩
                simp only [substAssign, sigma1, parity_singleton, Bool.xor_false, ha]
          · apply hM_from_amoL u j (by omega); intro a hdisj; rw [hsat_iff]
            rcases hdisj with hp | ha
            · refine ⟨(⟨(Sum.inl ⟨u, j⟩, Sum.inr ⟨u, t2⟩), (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inr hjt⟩⟩, false), by simp, ?_⟩
              have ht_eq : t2.val = j.val - 1 := by omega
              simp only [substAssign, sigma1, show ¬ (j.val = t2.val) by omega, ↓reduceIte, Bool.xor_false]; rw [ht_eq, hp]
            · refine ⟨(⟨(Sum.inl ⟨u, j⟩, Sum.inl ⟨v1, j1⟩), (mem_G1_iff G₀ _ _).mpr h1⟩, false), by simp, ?_⟩
              simp only [substAssign, sigma1, parity_singleton, Bool.xor_false, ha]
        · rcases h1 with ⟨rfl, hjt | hjt⟩
          · by_cases hj0 : j.val = 0
            · apply hM_taut; intro a; rw [hsat_iff]
              have ht0 : t1.val = 0 := by omega
              have hj_eq : j = ⟨0, by omega⟩ := Fin.ext hj0
              cases ha : a (portEdgeL G₀ u j)
              · refine ⟨(⟨(Sum.inl ⟨u, j⟩, Sum.inl ⟨v2, j2⟩), (mem_G1_iff G₀ _ _).mpr h2⟩, false), by simp, ?_⟩
                simp only [substAssign, sigma1, parity_singleton, Bool.xor_false, ha]
              · refine ⟨(⟨(Sum.inl ⟨u, j⟩, Sum.inr ⟨u, t1⟩), (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inl hjt⟩⟩, false), by simp, ?_⟩
                simp only [substAssign, sigma1, hjt, ↓reduceIte, ht0, prefSet_zero (by omega) (portEdgeL G₀ u),
                  parity_singleton, ← hj_eq, ha]; rfl
            · apply hM_from_amoL u j (by omega); intro a hdisj; rw [hsat_iff]
              rcases hdisj with hp | ha
              · cases ha' : a (portEdgeL G₀ u j)
                · refine ⟨(⟨(Sum.inl ⟨u, j⟩, Sum.inl ⟨v2, j2⟩), (mem_G1_iff G₀ _ _).mpr h2⟩, false), by simp, ?_⟩
                  simp only [substAssign, sigma1, parity_singleton, Bool.xor_false, ha']
                · refine ⟨(⟨(Sum.inl ⟨u, j⟩, Sum.inr ⟨u, t1⟩), (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inl hjt⟩⟩, false), by simp, ?_⟩
                  simp only [substAssign, sigma1, hjt, ↓reduceIte]
                  have hts : t1.val = (j.val - 1) + 1 := by omega
                  have hjeq : (⟨(j.val - 1) + 1, by omega⟩ : Fin (degL G₀ u)) = j := Fin.ext (by (try dsimp); omega)
                  rw [hts, prefSet_succ (portEdgeL G₀ u) (j.val - 1) (by omega),
                    parity_insert a _ _ (not_mem_prefSet (portEdgeL_inj G₀ u) (j.val - 1) (by omega)),
                    hjeq, ha', hp]; rfl
              · refine ⟨(⟨(Sum.inl ⟨u, j⟩, Sum.inl ⟨v2, j2⟩), (mem_G1_iff G₀ _ _).mpr h2⟩, false), by simp, ?_⟩
                simp only [substAssign, sigma1, parity_singleton, Bool.xor_false, ha]
          · apply hM_from_amoL u j (by omega); intro a hdisj; rw [hsat_iff]
            rcases hdisj with hp | ha
            · refine ⟨(⟨(Sum.inl ⟨u, j⟩, Sum.inr ⟨u, t1⟩), (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inr hjt⟩⟩, false), by simp, ?_⟩
              have ht_eq : t1.val = j.val - 1 := by omega
              simp only [substAssign, sigma1, show ¬ (j.val = t1.val) by omega, ↓reduceIte, Bool.xor_false]; rw [ht_eq, hp]
            · refine ⟨(⟨(Sum.inl ⟨u, j⟩, Sum.inl ⟨v2, j2⟩), (mem_G1_iff G₀ _ _).mpr h2⟩, false), by simp, ?_⟩
              simp only [substAssign, sigma1, parity_singleton, Bool.xor_false, ha]
        · rcases h1 with ⟨rfl, hjt1 | hjt1⟩ <;> rcases h2 with ⟨rfl, hjt2 | hjt2⟩
          · exfalso; apply hne2; congr 2; exact Fin.ext (by (try dsimp); omega)
          · apply hM_from_amoL u j (by omega); intro a hdisj; rw [hsat_iff]
            rcases hdisj with hp | ha
            · refine ⟨(⟨(Sum.inl ⟨u, j⟩, Sum.inr ⟨u, t2⟩), (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inr hjt2⟩⟩, false), by simp, ?_⟩
              have ht2_eq : t2.val = j.val - 1 := by omega
              simp only [substAssign, sigma1, show ¬ (j.val = t2.val) by omega, ↓reduceIte, Bool.xor_false]; rw [ht2_eq, hp]
            · cases hp' : parity a (prefSet (portEdgeL G₀ u) (j.val - 1))
              · refine ⟨(⟨(Sum.inl ⟨u, j⟩, Sum.inr ⟨u, t2⟩), (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inr hjt2⟩⟩, false), by simp, ?_⟩
                have ht2_eq : t2.val = j.val - 1 := by omega
                simp only [substAssign, sigma1, show ¬ (j.val = t2.val) by omega, ↓reduceIte, Bool.xor_false]; rw [ht2_eq, hp']
              · refine ⟨(⟨(Sum.inl ⟨u, j⟩, Sum.inr ⟨u, t1⟩), (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inl hjt1⟩⟩, false), by simp, ?_⟩
                simp only [substAssign, sigma1, hjt1, ↓reduceIte]
                have hts : t1.val = (j.val - 1) + 1 := by omega
                have hjeq : (⟨(j.val - 1) + 1, by omega⟩ : Fin (degL G₀ u)) = j := Fin.ext (by (try dsimp); omega)
                rw [hts, prefSet_succ (portEdgeL G₀ u) (j.val - 1) (by omega),
                  parity_insert a _ _ (not_mem_prefSet (portEdgeL_inj G₀ u) (j.val - 1) (by omega)),
                  hjeq, ha, hp']; rfl
          · apply hM_from_amoL u j (by omega); intro a hdisj; rw [hsat_iff]
            rcases hdisj with hp | ha
            · refine ⟨(⟨(Sum.inl ⟨u, j⟩, Sum.inr ⟨u, t1⟩), (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inr hjt1⟩⟩, false), by simp, ?_⟩
              have ht1_eq : t1.val = j.val - 1 := by omega
              simp only [substAssign, sigma1, show ¬ (j.val = t1.val) by omega, ↓reduceIte, Bool.xor_false]; rw [ht1_eq, hp]
            · cases hp' : parity a (prefSet (portEdgeL G₀ u) (j.val - 1))
              · refine ⟨(⟨(Sum.inl ⟨u, j⟩, Sum.inr ⟨u, t1⟩), (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inr hjt1⟩⟩, false), by simp, ?_⟩
                have ht1_eq : t1.val = j.val - 1 := by omega
                simp only [substAssign, sigma1, show ¬ (j.val = t1.val) by omega, ↓reduceIte, Bool.xor_false]; rw [ht1_eq, hp']
              · refine ⟨(⟨(Sum.inl ⟨u, j⟩, Sum.inr ⟨u, t2⟩), (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inl hjt2⟩⟩, false), by simp, ?_⟩
                simp only [substAssign, sigma1, hjt2, ↓reduceIte]
                have hts : t2.val = (j.val - 1) + 1 := by omega
                have hjeq : (⟨(j.val - 1) + 1, by omega⟩ : Fin (degL G₀ u)) = j := Fin.ext (by (try dsimp); omega)
                rw [hts, prefSet_succ (portEdgeL G₀ u) (j.val - 1) (by omega),
                  parity_insert a _ _ (not_mem_prefSet (portEdgeL_inj G₀ u) (j.val - 1) (by omega)),
                  hjeq, ha, hp']; rfl
          · exfalso; apply hne2; congr 2; exact Fin.ext (by (try dsimp); omega)
      · rcases y1 with ⟨v1, j1⟩ | ⟨u1, t1⟩ <;> rcases y2 with ⟨v2, j2⟩ | ⟨u2, t2⟩
        all_goals simp only [adj1Prop] at h1 h2
        all_goals try exact False.elim h1
        all_goals try exact False.elim h2
        rcases h1 with ⟨rfl, h1 | h1⟩ <;> rcases h2 with ⟨rfl, h2 | h2⟩
        · exfalso; apply hne2; congr 2; exact Fin.ext (by omega)
        · apply hM_taut; intro a; rw [hsat_iff]
          cases hp : parity a (prefSet (portEdgeR G₀ v2) t.val)
          · refine ⟨(⟨(Sum.inr ⟨v2, t⟩, Sum.inl ⟨v2, j2⟩), (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inr h2⟩⟩, false), by simp, ?_⟩
            simp only [substAssign, sigma1, show ¬ (j2.val = t.val) by omega, ↓reduceIte, Bool.xor_false, hp]
          · refine ⟨(⟨(Sum.inr ⟨v2, t⟩, Sum.inl ⟨v2, j1⟩), (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inl h1⟩⟩, false), by simp, ?_⟩
            simp only [substAssign, sigma1, h1, ↓reduceIte, hp]; rfl
        · apply hM_taut; intro a; rw [hsat_iff]
          cases hp : parity a (prefSet (portEdgeR G₀ v2) t.val)
          · refine ⟨(⟨(Sum.inr ⟨v2, t⟩, Sum.inl ⟨v2, j1⟩), (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inr h1⟩⟩, false), by simp, ?_⟩
            simp only [substAssign, sigma1, show ¬ (j1.val = t.val) by omega, ↓reduceIte, Bool.xor_false, hp]
          · refine ⟨(⟨(Sum.inr ⟨v2, t⟩, Sum.inl ⟨v2, j2⟩), (mem_G1_iff G₀ _ _).mpr ⟨rfl, Or.inl h2⟩⟩, false), by simp, ?_⟩
            simp only [substAssign, sigma1, h2, ↓reduceIte, hp]; rfl
        · exfalso; apply hne2; congr 2; exact Fin.ext (by omega)
  have hsim := affine_sim k 1200 hk (funGraphPHP G₀) (genGraphPHP (G1 G₀)) A₀ hA₀ (sigma1 G₀) hax π₁ hπ₁
  simpa using hsim

end Subcubicize

section StretchAndEar

open scoped Classical

variable {L R : Type} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
variable (G : GenBip L R) (s : GenEdge G → ℕ) (earLen : ℕ) (uStar : L) (vStar : R)

abbrev L2 (G : GenBip L R) (s : GenEdge G → ℕ) (earLen : ℕ) : Type :=
  L ⊕ (Σ e : GenEdge G, Fin (s e)) ⊕ Fin earLen

abbrev R2 (G : GenBip L R) (s : GenEdge G → ℕ) (earLen : ℕ) : Type :=
  R ⊕ (Σ e : GenEdge G, Fin (s e)) ⊕ Fin earLen

def adj2Prop (x : L2 G s earLen) (y : R2 G s earLen) : Prop :=
  match x, y with
  | Sum.inl u, Sum.inr (Sum.inl ⟨e, r⟩) => u = e.1.1 ∧ r.val = 0
  | Sum.inr (Sum.inl ⟨e, r⟩), Sum.inr (Sum.inl ⟨e', r'⟩) =>
      e = e' ∧ (r.val = r'.val ∨ r.val + 1 = r'.val)
  | Sum.inr (Sum.inl ⟨e, r⟩), Sum.inl v => v = e.1.2 ∧ r.val + 1 = s e
  | Sum.inl u, Sum.inr (Sum.inr r) => u = uStar ∧ r.val = 0
  | Sum.inr (Sum.inr r), Sum.inr (Sum.inr r') => r.val = r'.val ∨ r.val + 1 = r'.val
  | Sum.inr (Sum.inr r), Sum.inl v => v = vStar ∧ r.val + 1 = earLen
  | _, _ => False

noncomputable def G2 : GenBip (L2 G s earLen) (R2 G s earLen) := by
  classical
  exact fun x => Finset.univ.filter (fun y => adj2Prop G s earLen uStar vStar x y)

lemma mem_G2_iff (x : L2 G s earLen) (y : R2 G s earLen) :
    y ∈ G2 G s earLen uStar vStar x ↔ adj2Prop G s earLen uStar vStar x y := by
  classical
  simp [G2]

lemma stretch_card_LR (hLR : Fintype.card L = Fintype.card R + 1) :
    Fintype.card (L2 G s earLen) = Fintype.card (R2 G s earLen) + 1 := by
  simp only [L2, R2, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]
  omega

lemma stretch_deg_and_edges (hs : ∀ e, 1 ≤ s e)
    (hdegL : ∀ u : L, 2 ≤ (G u).card ∧ (G u).card ≤ 3)
    (hdegR : ∀ v : R, 2 ≤ (gRightNbrs G v).card ∧ (gRightNbrs G v).card ≤ 3)
    (huStar : earLen = 0 ∨ (G uStar).card = 2)
    (hvStar : earLen = 0 ∨ (gRightNbrs G vStar).card = 2) :
    (∀ x : L2 G s earLen, 2 ≤ (G2 G s earLen uStar vStar x).card ∧ (G2 G s earLen uStar vStar x).card ≤ 3) ∧
    (∀ y : R2 G s earLen, 2 ≤ (gRightNbrs (G2 G s earLen uStar vStar) y).card ∧
      (gRightNbrs (G2 G s earLen uStar vStar) y).card ≤ 3) ∧
    Fintype.card (GenEdge (G2 G s earLen uStar vStar)) =
      (∑ e : GenEdge G, (2 * s e + 1)) + (if 0 < earLen then 2 * earLen + 1 else 0) := by
  classical
  have hcardL_inl : ∀ u : L, (G2 G s earLen uStar vStar (Sum.inl u)).card =
      (G u).card + (if u = uStar ∧ 0 < earLen then 1 else 0) := by
    intro u
    let s1 : Finset (R2 G s earLen) :=
      (G u).attach.image (fun v => Sum.inr (Sum.inl ⟨⟨(u, v.1), v.2⟩, ⟨0, hs _⟩⟩))
    let s2 : Finset (R2 G s earLen) :=
      if h : u = uStar ∧ 0 < earLen then {Sum.inr (Sum.inr ⟨0, h.2⟩)} else ∅
    have heq : G2 G s earLen uStar vStar (Sum.inl u) = s1 ∪ s2 := by
      ext y
      rw [mem_G2_iff]
      rcases y with v | ⟨e, r⟩ | r
      · simp only [adj2Prop, Finset.mem_union, s1, s2]
        constructor
        · intro h; exact False.elim h
        · rintro (h | h)
          · simp at h
          · split_ifs at h <;> simp at h
      · simp only [adj2Prop, Finset.mem_union, s1, Finset.mem_image, Finset.mem_attach, true_and,
          Subtype.exists]
        have hnot2 : Sum.inr (Sum.inl ⟨e, r⟩) ∉ s2 := by dsimp [s2]; split_ifs <;> simp
        simp only [hnot2, or_false]
        constructor
        · rintro ⟨hu, hr0⟩
          rcases e with ⟨⟨u', v'⟩, hv'⟩
          dsimp at hu; subst hu
          refine ⟨v', hv', ?_⟩
          congr 2; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext hr0.symm
        · rintro ⟨v', hv', h⟩
          injection h with h1; injection h1 with hsig
          rcases Sigma.mk.inj hsig with ⟨rfl, hr⟩
          exact ⟨rfl, (congrArg Fin.val (eq_of_heq hr)).symm⟩
      · simp only [adj2Prop, Finset.mem_union, s2]
        have hnot1 : Sum.inr (Sum.inr r) ∉ s1 := by simp [s1]
        simp only [hnot1, false_or]
        constructor
        · rintro ⟨hu, hr0⟩
          have hcond : u = uStar ∧ 0 < earLen := ⟨hu, by omega⟩
          simp only [hcond, and_self, ↓reduceDIte, Finset.mem_singleton]
          congr 2; exact Fin.ext hr0
        · intro h
          by_cases hcond : u = uStar ∧ 0 < earLen
          · simp only [hcond, and_self, ↓reduceDIte, Finset.mem_singleton] at h
            injection h with h1; injection h1 with h2
            exact ⟨hcond.1, congrArg Fin.val h2⟩
          · simp [hcond] at h
    have hdisj : Disjoint s1 s2 := by
      rw [Finset.disjoint_left]
      intro y hy1 hy2
      rcases Finset.mem_image.mp hy1 with ⟨v, _, rfl⟩
      dsimp [s2] at hy2; split_ifs at hy2 <;> simp at hy2
    have hc1 : s1.card = (G u).card := by
      rw [Finset.card_image_of_injective, Finset.card_attach]
      intro a b hab
      injection hab with h1; injection h1 with h2
      have h3 := (Sigma.mk.inj h2).1
      exact Subtype.ext (congrArg (fun e : GenEdge G => e.1.2) h3)
    have hc2 : s2.card = if u = uStar ∧ 0 < earLen then 1 else 0 := by
      dsimp [s2]; split_ifs <;> simp
    rw [heq, Finset.card_union_of_disjoint hdisj, hc1, hc2]
  have hcardL_mid : ∀ (e : GenEdge G) (r : Fin (s e)),
      (G2 G s earLen uStar vStar (Sum.inr (Sum.inl ⟨e, r⟩))).card = 2 := by
    intro e r
    let y1 : R2 G s earLen := Sum.inr (Sum.inl ⟨e, r⟩)
    let y2 : R2 G s earLen :=
      if h : r.val + 1 < s e then Sum.inr (Sum.inl ⟨e, ⟨r.val + 1, h⟩⟩) else Sum.inl e.1.2
    have hne : y1 ≠ y2 := by
      dsimp [y1, y2]; split_ifs with h
      · intro heq; injection heq with h1; injection h1 with h2
        have hv := congrArg Fin.val (eq_of_heq (Sigma.mk.inj h2).2); dsimp at hv; omega
      · simp
    have heq : G2 G s earLen uStar vStar (Sum.inr (Sum.inl ⟨e, r⟩)) = {y1, y2} := by
      ext y
      rw [mem_G2_iff]
      rcases y with v | ⟨e', r'⟩ | r'
      · simp only [adj2Prop, Finset.mem_insert, Finset.mem_singleton, y1, y2]
        constructor
        · rintro ⟨rfl, hr⟩
          right
          have hnot : ¬ (r.val + 1 < s e) := by omega
          simp [hnot]
        · rintro (h | h)
          · simp at h
          · split_ifs at h with hlt
            injection h with hv
            exact ⟨hv, by omega⟩
      · simp only [adj2Prop, Finset.mem_insert, Finset.mem_singleton, y1, y2]
        constructor
        · rintro ⟨rfl, h1 | h2⟩
          · left; congr 2; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext h1.symm
          · right
            have hlt : r.val + 1 < s e := by omega
            simp only [hlt, ↓reduceDIte]
            congr 2; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext h2.symm
        · rintro (h | h)
          · injection h with h1; injection h1 with h2
            rcases Sigma.mk.inj h2 with ⟨rfl, hr⟩
            exact ⟨rfl, Or.inl (congrArg Fin.val (eq_of_heq hr)).symm⟩
          · split_ifs at h with hlt
            injection h with h1; injection h1 with h2
            rcases Sigma.mk.inj h2 with ⟨rfl, hr⟩
            exact ⟨rfl, Or.inr (congrArg Fin.val (eq_of_heq hr)).symm⟩
      · simp only [adj2Prop, Finset.mem_insert, Finset.mem_singleton, y1, y2]
        constructor
        · intro h; exact False.elim h
        · rintro (h | h)
          · simp at h
          · split_ifs at h <;> simp at h
    rw [heq, Finset.card_pair hne]
  have hcardL_ear : ∀ (r : Fin earLen),
      (G2 G s earLen uStar vStar (Sum.inr (Sum.inr r))).card = 2 := by
    intro r
    let y1 : R2 G s earLen := Sum.inr (Sum.inr r)
    let y2 : R2 G s earLen :=
      if h : r.val + 1 < earLen then Sum.inr (Sum.inr ⟨r.val + 1, h⟩) else Sum.inl vStar
    have hne : y1 ≠ y2 := by
      dsimp [y1, y2]; split_ifs with h
      · intro heq; injection heq with h1; injection h1 with h2
        have hv := congrArg Fin.val h2; dsimp at hv; omega
      · simp
    have heq : G2 G s earLen uStar vStar (Sum.inr (Sum.inr r)) = {y1, y2} := by
      ext y
      rw [mem_G2_iff]
      rcases y with v | ⟨e', r'⟩ | r'
      · simp only [adj2Prop, Finset.mem_insert, Finset.mem_singleton, y1, y2]
        constructor
        · rintro ⟨rfl, hr⟩
          right
          have hnot : ¬ (r.val + 1 < earLen) := by omega
          simp [hnot]
        · rintro (h | h)
          · simp at h
          · split_ifs at h with hlt
            injection h with hv
            exact ⟨hv, by omega⟩
      · simp only [adj2Prop, Finset.mem_insert, Finset.mem_singleton, y1, y2]
        constructor
        · intro h; exact False.elim h
        · rintro (h | h)
          · simp at h
          · split_ifs at h <;> simp at h
      · simp only [adj2Prop, Finset.mem_insert, Finset.mem_singleton, y1, y2]
        constructor
        · rintro (h1 | h2)
          · left; congr 2; exact Fin.ext h1.symm
          · right
            have hlt : r.val + 1 < earLen := by omega
            simp only [hlt, ↓reduceDIte]
            congr 2; exact Fin.ext h2.symm
        · rintro (h | h)
          · injection h with h1; injection h1 with h2
            exact Or.inl (congrArg Fin.val h2).symm
          · split_ifs at h with hlt
            injection h with h1; injection h1 with h2
            exact Or.inr (congrArg Fin.val h2).symm
    rw [heq, Finset.card_pair hne]
  have hcardR_inl : ∀ v : R, (gRightNbrs (G2 G s earLen uStar vStar) (Sum.inl v)).card =
      (gRightNbrs G v).card + (if v = vStar ∧ 0 < earLen then 1 else 0) := by
    intro v
    let s1 : Finset (L2 G s earLen) :=
      (gRightNbrs G v).attach.image (fun u =>
        let e : GenEdge G := ⟨(u.1, v), (mem_gRightNbrs_iff G v u.1).mp u.2⟩
        Sum.inr (Sum.inl ⟨e, ⟨s e - 1, by have := hs e; omega⟩⟩))
    let s2 : Finset (L2 G s earLen) :=
      if h : v = vStar ∧ 0 < earLen then {Sum.inr (Sum.inr ⟨earLen - 1, by omega⟩)} else ∅
    have heq : gRightNbrs (G2 G s earLen uStar vStar) (Sum.inl v) = s1 ∪ s2 := by
      ext x
      simp only [gRightNbrs, Finset.mem_filter, Finset.mem_univ, true_and, mem_G2_iff]
      rcases x with u | ⟨e, r⟩ | r
      · simp only [adj2Prop, Finset.mem_union, s1, s2]
        constructor
        · intro h; exact False.elim h
        · rintro (h | h)
          · simp at h
          · split_ifs at h <;> simp at h
      · simp only [adj2Prop, Finset.mem_union, s1, Finset.mem_image, Finset.mem_attach, true_and,
          Subtype.exists]
        have hnot2 : Sum.inr (Sum.inl ⟨e, r⟩) ∉ s2 := by dsimp [s2]; split_ifs <;> simp
        simp only [hnot2, or_false]
        constructor
        · rintro ⟨hv, hr⟩
          rcases e with ⟨⟨u', v'⟩, hv'⟩
          dsimp at hv; subst hv
          refine ⟨u', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv'⟩, ?_⟩
          congr 2; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext (by dsimp at hr ⊢; omega)
        · rintro ⟨u', hu', h⟩
          injection h with h1; injection h1 with hsig
          rcases Sigma.mk.inj hsig with ⟨rfl, hr⟩
          have hv := congrArg Fin.val (eq_of_heq hr)
          have hse := hs ⟨(u', v), (Finset.mem_filter.mp hu').2⟩
          exact ⟨rfl, by dsimp at hv ⊢; omega⟩
      · simp only [adj2Prop, Finset.mem_union, s2]
        have hnot1 : Sum.inr (Sum.inr r) ∉ s1 := by simp [s1]
        simp only [hnot1, false_or]
        constructor
        · rintro ⟨hv, hr⟩
          have hcond : v = vStar ∧ 0 < earLen := ⟨hv, by omega⟩
          simp only [hcond, and_self, ↓reduceDIte, Finset.mem_singleton]
          congr 2; exact Fin.ext (by (try dsimp); omega)
        · intro h
          by_cases hcond : v = vStar ∧ 0 < earLen
          · simp only [hcond, and_self, ↓reduceDIte, Finset.mem_singleton] at h
            injection h with h1; injection h1 with h2
            have hv := congrArg Fin.val h2
            exact ⟨hcond.1, by dsimp at hv; omega⟩
          · simp [hcond] at h
    have hdisj : Disjoint s1 s2 := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rcases Finset.mem_image.mp hx1 with ⟨u, _, rfl⟩
      dsimp [s2] at hx2; split_ifs at hx2 <;> simp at hx2
    have hc1 : s1.card = (gRightNbrs G v).card := by
      rw [Finset.card_image_of_injective, Finset.card_attach]
      intro a b hab
      injection hab with h1; injection h1 with h2
      have h3 := (Sigma.mk.inj h2).1
      exact Subtype.ext (congrArg (fun e : GenEdge G => e.1.1) h3)
    have hc2 : s2.card = if v = vStar ∧ 0 < earLen then 1 else 0 := by
      dsimp [s2]; split_ifs <;> simp
    rw [heq, Finset.card_union_of_disjoint hdisj, hc1, hc2]
  have hcardR_mid : ∀ (e : GenEdge G) (r : Fin (s e)),
      (gRightNbrs (G2 G s earLen uStar vStar) (Sum.inr (Sum.inl ⟨e, r⟩))).card = 2 := by
    intro e r
    let x1 : L2 G s earLen := Sum.inr (Sum.inl ⟨e, r⟩)
    let x2 : L2 G s earLen :=
      if h : 0 < r.val then Sum.inr (Sum.inl ⟨e, ⟨r.val - 1, by omega⟩⟩) else Sum.inl e.1.1
    have hne : x1 ≠ x2 := by
      dsimp [x1, x2]; split_ifs with h
      · intro heq; injection heq with h1; injection h1 with h2
        have hv := congrArg Fin.val (eq_of_heq (Sigma.mk.inj h2).2); dsimp at hv; omega
      · simp
    have heq : gRightNbrs (G2 G s earLen uStar vStar) (Sum.inr (Sum.inl ⟨e, r⟩)) = {x1, x2} := by
      ext x
      simp only [gRightNbrs, Finset.mem_filter, Finset.mem_univ, true_and, mem_G2_iff]
      rcases x with u | ⟨e', r'⟩ | r'
      · simp only [adj2Prop, Finset.mem_insert, Finset.mem_singleton, x1, x2]
        constructor
        · rintro ⟨rfl, hr0⟩
          right; have hnot : ¬ (0 < r.val) := by omega
          simp [hnot]
        · rintro (h | h)
          · simp at h
          · split_ifs at h with hpos
            injection h with hu; exact ⟨hu, by omega⟩
      · simp only [adj2Prop, Finset.mem_insert, Finset.mem_singleton, x1, x2]
        constructor
        · rintro ⟨rfl, h1 | h2⟩
          · left; congr 2; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext h1
          · right
            have hpos : 0 < r.val := by omega
            simp only [hpos, ↓reduceDIte]
            congr 2; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext (by (try dsimp); omega)
        · rintro (h | h)
          · injection h with h1; injection h1 with h2
            rcases Sigma.mk.inj h2 with ⟨rfl, hr⟩
            exact ⟨rfl, Or.inl (congrArg Fin.val (eq_of_heq hr))⟩
          · split_ifs at h with hpos
            injection h with h1; injection h1 with h2
            rcases Sigma.mk.inj h2 with ⟨rfl, hr⟩
            have hv := congrArg Fin.val (eq_of_heq hr)
            exact ⟨rfl, Or.inr (by dsimp at hv; omega)⟩
      · simp only [adj2Prop, Finset.mem_insert, Finset.mem_singleton, x1, x2]
        constructor
        · intro h; exact False.elim h
        · rintro (h | h)
          · simp at h
          · split_ifs at h <;> simp at h
    rw [heq, Finset.card_pair hne]
  have hcardR_ear : ∀ (r : Fin earLen),
      (gRightNbrs (G2 G s earLen uStar vStar) (Sum.inr (Sum.inr r))).card = 2 := by
    intro r
    let x1 : L2 G s earLen := Sum.inr (Sum.inr r)
    let x2 : L2 G s earLen :=
      if h : 0 < r.val then Sum.inr (Sum.inr ⟨r.val - 1, by omega⟩) else Sum.inl uStar
    have hne : x1 ≠ x2 := by
      dsimp [x1, x2]; split_ifs with h
      · intro heq; injection heq with h1; injection h1 with h2
        have hv := congrArg Fin.val h2; dsimp at hv; omega
      · simp
    have heq : gRightNbrs (G2 G s earLen uStar vStar) (Sum.inr (Sum.inr r)) = {x1, x2} := by
      ext x
      simp only [gRightNbrs, Finset.mem_filter, Finset.mem_univ, true_and, mem_G2_iff]
      rcases x with u | ⟨e', r'⟩ | r'
      · simp only [adj2Prop, Finset.mem_insert, Finset.mem_singleton, x1, x2]
        constructor
        · rintro ⟨rfl, hr0⟩
          right; have hnot : ¬ (0 < r.val) := by omega
          simp [hnot]
        · rintro (h | h)
          · simp at h
          · split_ifs at h with hpos
            injection h with hu; exact ⟨hu, by omega⟩
      · simp only [adj2Prop, Finset.mem_insert, Finset.mem_singleton, x1, x2]
        constructor
        · intro h; exact False.elim h
        · rintro (h | h)
          · simp at h
          · split_ifs at h <;> simp at h
      · simp only [adj2Prop, Finset.mem_insert, Finset.mem_singleton, x1, x2]
        constructor
        · rintro (h1 | h2)
          · left; congr 2; exact Fin.ext h1
          · right
            have hpos : 0 < r.val := by omega
            simp only [hpos, ↓reduceDIte]
            congr 2; exact Fin.ext (by (try dsimp); omega)
        · rintro (h | h)
          · injection h with h1; injection h1 with h2
            exact Or.inl (congrArg Fin.val h2)
          · split_ifs at h with hpos
            injection h with h1; injection h1 with h2
            have hv := congrArg Fin.val h2
            exact Or.inr (by dsimp at hv; omega)
    rw [heq, Finset.card_pair hne]
  refine ⟨?_, ?_, ?_⟩
  · rintro (u | ⟨e, r⟩ | r)
    · rw [hcardL_inl u]
      have hd := hdegL u
      split_ifs with hcond
      · rcases huStar with h0 | hu2
        · omega
        · rw [hcond.1, hu2]; omega
      · exact hd
    · rw [hcardL_mid e r]; omega
    · rw [hcardL_ear r]; omega
  · rintro (v | ⟨e, r⟩ | r)
    · rw [hcardR_inl v]
      have hd := hdegR v
      split_ifs with hcond
      · rcases hvStar with h0 | hv2
        · omega
        · rw [hcond.1, hv2]; omega
      · exact hd
    · rw [hcardR_mid e r]; omega
    · rw [hcardR_ear r]; omega
  · have hcard_eq : Fintype.card (GenEdge (G2 G s earLen uStar vStar)) =
        ∑ x : L2 G s earLen, (G2 G s earLen uStar vStar x).card := by
      convert card_genEdge_eq_sum_left (G2 G s earLen uStar vStar)
    rw [hcard_eq, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sigma]
    simp_rw [hcardL_inl, hcardL_mid, hcardL_ear]
    rw [Finset.sum_add_distrib]
    have hsumG : ∑ u : L, (G u).card = ∑ _e : GenEdge G, 1 := by
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
      convert (card_genEdge_eq_sum_left G).symm
    have hsumMid : ∑ e : GenEdge G, ∑ _r : Fin (s e), 2 = ∑ e : GenEdge G, 2 * s e := by
      refine Finset.sum_congr rfl (fun e _ => by simp [mul_comm])
    have hsumU : ∑ u : L, (if u = uStar ∧ 0 < earLen then 1 else 0) = if 0 < earLen then 1 else 0 := by
      by_cases he : 0 < earLen
      · simp [he]
      · simp [he]
    have hsumEar : ∑ _r : Fin earLen, 2 = 2 * earLen := by simp [mul_comm]
    rw [hsumG, hsumMid, hsumU, hsumEar]
    have hcomb : (∑ _e : GenEdge G, 1) + (∑ e : GenEdge G, 2 * s e) =
        ∑ e : GenEdge G, (2 * s e + 1) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun e _ => by omega)
    split_ifs with he
    · omega
    · have : earLen = 0 := by omega
      subst this; omega

lemma stretch_conn (hs : ∀ e, 1 ≤ s e) (hconn : GenConn G) :
    GenConn (G2 G s earLen uStar vStar) := by
  intro f hf
  have hedge_chain : ∀ (e : GenEdge G),
      (∀ r : Fin (s e), f (Sum.inr (Sum.inr (Sum.inl ⟨e, r⟩))) = f (Sum.inl (Sum.inl e.1.1)) ∧
        f (Sum.inl (Sum.inr (Sum.inl ⟨e, r⟩))) = f (Sum.inl (Sum.inl e.1.1))) ∧
      f (Sum.inl (Sum.inl e.1.1)) = f (Sum.inr (Sum.inl e.1.2)) := by
    intro e
    have hstep : ∀ (r : Fin (s e)),
        f (Sum.inr (Sum.inr (Sum.inl ⟨e, r⟩))) = f (Sum.inl (Sum.inl e.1.1)) ∧
        f (Sum.inl (Sum.inr (Sum.inl ⟨e, r⟩))) = f (Sum.inl (Sum.inl e.1.1)) := by
      rintro ⟨r, hr⟩
      induction r with
      | zero =>
        have h1 := hf (Sum.inl e.1.1) (Sum.inr (Sum.inl ⟨e, ⟨0, hr⟩⟩))
          ((mem_G2_iff G s earLen uStar vStar _ _).mpr ⟨rfl, rfl⟩)
        have h2 := hf (Sum.inr (Sum.inl ⟨e, ⟨0, hr⟩⟩)) (Sum.inr (Sum.inl ⟨e, ⟨0, hr⟩⟩))
          ((mem_G2_iff G s earLen uStar vStar _ _).mpr ⟨rfl, Or.inl rfl⟩)
        exact ⟨h1.symm, h2.trans h1.symm⟩
      | succ r ih =>
        have hprev := ih (by omega)
        have h1 := hf (Sum.inr (Sum.inl ⟨e, ⟨r, by omega⟩⟩)) (Sum.inr (Sum.inl ⟨e, ⟨r + 1, hr⟩⟩))
          ((mem_G2_iff G s earLen uStar vStar _ _).mpr ⟨rfl, Or.inr rfl⟩)
        have h2 := hf (Sum.inr (Sum.inl ⟨e, ⟨r + 1, hr⟩⟩)) (Sum.inr (Sum.inl ⟨e, ⟨r + 1, hr⟩⟩))
          ((mem_G2_iff G s earLen uStar vStar _ _).mpr ⟨rfl, Or.inl rfl⟩)
        have hR : f (Sum.inr (Sum.inr (Sum.inl ⟨e, ⟨r + 1, hr⟩⟩))) = f (Sum.inl (Sum.inl e.1.1)) :=
          h1.symm.trans hprev.2
        exact ⟨hR, h2.trans hR⟩
    refine ⟨hstep, ?_⟩
    have hse := hs e
    have hlast := hf (Sum.inr (Sum.inl ⟨e, ⟨s e - 1, by omega⟩⟩)) (Sum.inl e.1.2)
      ((mem_G2_iff G s earLen uStar vStar _ _).mpr ⟨rfl, by dsimp; omega⟩)
    exact (hstep ⟨s e - 1, by omega⟩).2.symm.trans hlast
  have hear_chain : ∀ (r : Fin earLen),
      f (Sum.inr (Sum.inr (Sum.inr r))) = f (Sum.inl (Sum.inl uStar)) ∧
      f (Sum.inl (Sum.inr (Sum.inr r))) = f (Sum.inl (Sum.inl uStar)) := by
    rintro ⟨r, hr⟩
    induction r with
    | zero =>
      have h1 := hf (Sum.inl uStar) (Sum.inr (Sum.inr ⟨0, hr⟩))
        ((mem_G2_iff G s earLen uStar vStar _ _).mpr ⟨rfl, rfl⟩)
      have h2 := hf (Sum.inr (Sum.inr ⟨0, hr⟩)) (Sum.inr (Sum.inr ⟨0, hr⟩))
        ((mem_G2_iff G s earLen uStar vStar _ _).mpr (Or.inl rfl))
      exact ⟨h1.symm, h2.trans h1.symm⟩
    | succ r ih =>
      have hprev := ih (by omega)
      have h1 := hf (Sum.inr (Sum.inr ⟨r, by omega⟩)) (Sum.inr (Sum.inr ⟨r + 1, hr⟩))
        ((mem_G2_iff G s earLen uStar vStar _ _).mpr (Or.inr rfl))
      have h2 := hf (Sum.inr (Sum.inr ⟨r + 1, hr⟩)) (Sum.inr (Sum.inr ⟨r + 1, hr⟩))
        ((mem_G2_iff G s earLen uStar vStar _ _).mpr (Or.inl rfl))
      have hR : f (Sum.inr (Sum.inr (Sum.inr ⟨r + 1, hr⟩))) = f (Sum.inl (Sum.inl uStar)) :=
        h1.symm.trans hprev.2
      exact ⟨hR, h2.trans hR⟩
  let f₀ : L ⊕ R → Bool := fun z => match z with
    | Sum.inl u => f (Sum.inl (Sum.inl u))
    | Sum.inr v => f (Sum.inr (Sum.inl v))
  have hf₀ : ∀ u, ∀ v ∈ G u, f₀ (Sum.inl u) = f₀ (Sum.inr v) := fun u v hv =>
    (hedge_chain ⟨(u, v), hv⟩).2
  have hbase := hconn f₀ hf₀
  have hval : ∀ z : L2 G s earLen ⊕ R2 G s earLen, f z = f (Sum.inl (Sum.inl uStar)) := by
    rintro ((u | ⟨e, r⟩ | r) | (v | ⟨e, r⟩ | r))
    · exact hbase (Sum.inl u) (Sum.inl uStar)
    · exact ((hedge_chain e).1 r).2.trans (hbase (Sum.inl e.1.1) (Sum.inl uStar))
    · exact (hear_chain r).2
    · exact hbase (Sum.inr v) (Sum.inl uStar)
    · exact ((hedge_chain e).1 r).1.trans (hbase (Sum.inl e.1.1) (Sum.inl uStar))
    · exact (hear_chain r).1
  intro x y
  rw [hval x, hval y]

set_option maxHeartbeats 1200000 in
lemma stretch_girth (t : ℕ) (ht : 1 ≤ t) (hs : ∀ e, t ≤ s e)
    (a : ℕ) (us : Fin (a + 2) ↪ L2 G s earLen) (vs : Fin (a + 2) ↪ R2 G s earLen)
    (hcyc : ∀ i, vs i ∈ G2 G s earLen uStar vStar (us i) ∧
      vs i ∈ G2 G s earLen uStar vStar (us (i + 1))) :
    (0 < earLen ∧ earLen ≤ a + 2) ∨
    ∃ (a₁ : ℕ) (us₁ : Fin (a₁ + 2) ↪ L) (vs₁ : Fin (a₁ + 2) ↪ R),
      2 * (a₁ + 2) * t ≤ a + 2 ∧ ∀ i, vs₁ i ∈ G (us₁ i) ∧ vs₁ i ∈ G (us₁ (i + 1)) := by
  classical
  have hse1 : ∀ e, 1 ≤ s e := fun e => le_trans ht (hs e)
  have hdeg2_prop_L : ∀ (x : L2 G s earLen) (y1 y2 : R2 G s earLen),
      y1 ≠ y2 →
      G2 G s earLen uStar vStar x = {y1, y2} →
      (∃ i : Fin (a + 2), us i = x) →
      (∃ j : Fin (a + 2), vs j = y1) ∧ (∃ j : Fin (a + 2), vs j = y2) := by
    intro x y1 y2 hne hnbrs ⟨i, hi⟩
    have h1 : vs i ∈ ({y1, y2} : Finset _) := by rw [← hnbrs, ← hi]; exact (hcyc i).1
    have h2 : vs (i - 1) ∈ ({y1, y2} : Finset _) := by
      rw [← hnbrs, ← hi]; simpa using (hcyc (i - 1)).2
    have hne_idx : i ≠ i - 1 := by
      intro h
      exact fin_add_one_ne_self (by omega : 2 ≤ a + 2) (i - 1) (by simpa [sub_add_cancel] using h.symm)
    have hvne : vs i ≠ vs (i - 1) := fun h => hne_idx (vs.injective h)
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hvne
    · exact ⟨⟨i, h1⟩, ⟨i - 1, h2⟩⟩
    · exact ⟨⟨i - 1, h2⟩, ⟨i, h1⟩⟩
    · exact absurd (h1.trans h2.symm) hvne
  have hdeg2_prop_R : ∀ (y : R2 G s earLen) (x1 x2 : L2 G s earLen),
      x1 ≠ x2 →
      gRightNbrs (G2 G s earLen uStar vStar) y = {x1, x2} →
      (∃ j : Fin (a + 2), vs j = y) →
      (∃ i : Fin (a + 2), us i = x1) ∧ (∃ i : Fin (a + 2), us i = x2) := by
    intro y x1 x2 hne hnbrs ⟨j, hj⟩
    have h1 : us j ∈ ({x1, x2} : Finset _) := by
      rw [← hnbrs, ← hj]
      simp only [gRightNbrs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hcyc j).1
    have h2 : us (j + 1) ∈ ({x1, x2} : Finset _) := by
      rw [← hnbrs, ← hj]
      simp only [gRightNbrs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hcyc j).2
    have hne_idx : j ≠ j + 1 := fun h => fin_add_one_ne_self (by omega : 2 ≤ a + 2) j h.symm
    have hune : us j ≠ us (j + 1) := fun h => hne_idx (us.injective h)
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hune
    · exact ⟨⟨j, h1⟩, ⟨j + 1, h2⟩⟩
    · exact ⟨⟨j + 1, h2⟩, ⟨j, h1⟩⟩
    · exact absurd (h1.trans h2.symm) hune
  have hear_nbrsL : ∀ r : Fin earLen,
      G2 G s earLen uStar vStar (Sum.inr (Sum.inr r)) =
        {Sum.inr (Sum.inr r),
          if h : r.val + 1 < earLen then Sum.inr (Sum.inr ⟨r.val + 1, h⟩) else Sum.inl vStar} := by
    intro r; ext y; rw [mem_G2_iff]
    rcases y with v | ⟨e', r'⟩ | r'
    · simp only [adj2Prop, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl, hr⟩; right; simp [show ¬ (r.val + 1 < earLen) by omega]
      · rintro (h | h); · simp at h
        · split_ifs at h with hlt
          injection h with hv; exact ⟨hv, by omega⟩
    · simp only [adj2Prop, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro h; exact False.elim h
      · rintro (h | h); · simp at h
        · split_ifs at h <;> simp at h
    · simp only [adj2Prop, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (h1 | h2)
        · left; congr 2; exact Fin.ext h1.symm
        · right; have hlt : r.val + 1 < earLen := by omega
          simp only [hlt, ↓reduceDIte]; congr 2; exact Fin.ext h2.symm
      · rintro (h | h)
        · injection h with h1; injection h1 with h2; exact Or.inl (congrArg Fin.val h2).symm
        · split_ifs at h with hlt
          injection h with h1; injection h1 with h2; exact Or.inr (congrArg Fin.val h2).symm
  have hear_nbrsR : ∀ r : Fin earLen,
      gRightNbrs (G2 G s earLen uStar vStar) (Sum.inr (Sum.inr r)) =
        {Sum.inr (Sum.inr r),
          if h : 0 < r.val then Sum.inr (Sum.inr ⟨r.val - 1, by omega⟩) else Sum.inl uStar} := by
    intro r; ext x; simp only [gRightNbrs, Finset.mem_filter, Finset.mem_univ, true_and, mem_G2_iff]
    rcases x with u | ⟨e', r'⟩ | r'
    · simp only [adj2Prop, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl, hr0⟩; right; simp [show ¬ (0 < r.val) by omega]
      · rintro (h | h); · simp at h
        · split_ifs at h with hpos
          injection h with hu; exact ⟨hu, by omega⟩
    · simp only [adj2Prop, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro h; exact False.elim h
      · rintro (h | h); · simp at h
        · split_ifs at h <;> simp at h
    · simp only [adj2Prop, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (h1 | h2)
        · left; congr 2; exact Fin.ext h1
        · right; have hpos : 0 < r.val := by omega
          simp only [hpos, ↓reduceDIte]; congr 2; exact Fin.ext (by (try dsimp); omega)
      · rintro (h | h)
        · injection h with h1; injection h1 with h2; exact Or.inl (congrArg Fin.val h2)
        · split_ifs at h with hpos
          injection h with h1; injection h1 with h2
          have hv := congrArg Fin.val h2; exact Or.inr (by dsimp at hv; omega)
  by_cases hear : (∃ i : Fin (a + 2), ∃ r : Fin earLen, us i = Sum.inr (Sum.inr r)) ∨
      (∃ j : Fin (a + 2), ∃ r : Fin earLen, vs j = Sum.inr (Sum.inr r))
  · left
    have hL_from_R : ∀ r : Fin earLen, (∃ j, vs j = Sum.inr (Sum.inr r)) →
        ∃ i, us i = Sum.inr (Sum.inr r) := by
      intro r hr
      have hne : (Sum.inr (Sum.inr r) : L2 G s earLen) ≠
          (if h : 0 < r.val then Sum.inr (Sum.inr ⟨r.val - 1, by omega⟩) else Sum.inl uStar) := by
        split_ifs with h
        · intro heq; injection heq with h1; injection h1 with h2
          have hv := congrArg Fin.val h2; dsimp at hv; omega
        · simp
      exact (hdeg2_prop_R _ _ _ hne (hear_nbrsR r) hr).1
    have hsomeL : ∃ r0 : Fin earLen, ∃ i, us i = Sum.inr (Sum.inr r0) := by
      rcases hear with ⟨i, r, hi⟩ | ⟨j, r, hj⟩
      · exact ⟨r, i, hi⟩
      · exact ⟨r, hL_from_R r ⟨j, hj⟩⟩
    rcases hsomeL with ⟨r0, i0, hi0⟩
    have hear_pos : 0 < earLen := Nat.pos_of_ne_zero (fun h => by rw [h] at r0; exact Fin.elim0 r0)
    have hstep_up : ∀ r : Fin earLen, (h : r.val + 1 < earLen) →
        (∃ i, us i = Sum.inr (Sum.inr r)) → ∃ i, us i = Sum.inr (Sum.inr ⟨r.val + 1, h⟩) := by
      intro r h hr
      have hne : (Sum.inr (Sum.inr r) : R2 G s earLen) ≠
          (if h' : r.val + 1 < earLen then Sum.inr (Sum.inr ⟨r.val + 1, h'⟩) else Sum.inl vStar) := by
        simp only [h, ↓reduceDIte]
        intro heq; injection heq with h1; injection h1 with h2
        have hv := congrArg Fin.val h2; dsimp at hv; omega
      have hR := (hdeg2_prop_L _ _ _ hne (hear_nbrsL r) hr).2
      simp only [h, ↓reduceDIte] at hR
      exact hL_from_R ⟨r.val + 1, h⟩ hR
    have hstep_dn : ∀ r : Fin earLen, (h : 0 < r.val) →
        (∃ i, us i = Sum.inr (Sum.inr r)) → ∃ i, us i = Sum.inr (Sum.inr ⟨r.val - 1, by omega⟩) := by
      intro r h hr
      have hne1 : (Sum.inr (Sum.inr r) : R2 G s earLen) ≠
          (if h' : r.val + 1 < earLen then Sum.inr (Sum.inr ⟨r.val + 1, h'⟩) else Sum.inl vStar) := by
        split_ifs with h'
        · intro heq; injection heq with h1; injection h1 with h2
          have hv := congrArg Fin.val h2; dsimp at hv; omega
        · simp
      have hR := (hdeg2_prop_L _ _ _ hne1 (hear_nbrsL r) hr).1
      have hne2 : (Sum.inr (Sum.inr r) : L2 G s earLen) ≠
          (if h' : 0 < r.val then Sum.inr (Sum.inr ⟨r.val - 1, by omega⟩) else Sum.inl uStar) := by
        simp only [h, ↓reduceDIte]
        intro heq; injection heq with h1; injection h1 with h2
        have hv := congrArg Fin.val h2; dsimp at hv; omega
      have hL := (hdeg2_prop_R _ _ _ hne2 (hear_nbrsR r) hR).2
      simp only [h, ↓reduceDIte] at hL
      exact hL
    have hall : ∀ r : Fin earLen, ∃ i : Fin (a + 2), us i = Sum.inr (Sum.inr r) := by
      have h0 : ∃ i, us i = Sum.inr (Sum.inr ⟨0, hear_pos⟩) := by
        have hdn : ∀ d : ℕ, d ≤ r0.val → ∃ i, us i = Sum.inr (Sum.inr ⟨r0.val - d, by omega⟩) := by
          intro d
          induction d with
          | zero => intro _; simpa using ⟨i0, hi0⟩
          | succ d ih =>
            intro hd
            have hprev := ih (by omega)
            have h := hstep_dn ⟨r0.val - d, by omega⟩ (by (try dsimp); omega) hprev
            simpa [Nat.sub_sub] using h
        simpa using hdn r0.val le_rfl
      rintro ⟨r, hr⟩
      induction r with
      | zero => exact h0
      | succ r ih => exact hstep_up ⟨r, by omega⟩ hr (ih (by omega))
    choose f hf using hall
    have hfinj : Function.Injective f := by
      intro r1 r2 heq
      have h1 : Sum.inr (Sum.inr r1) = (Sum.inr (Sum.inr r2) : L2 G s earLen) := by
        rw [← hf r1, ← hf r2, heq]
      injection h1 with h2; injection h2
    have hle := Fintype.card_le_of_injective f hfinj
    simp only [Fintype.card_fin] at hle
    exact ⟨hear_pos, hle⟩
  · right
    push Not at hear
    have hno_earL : ∀ i : Fin (a + 2), ∀ r : Fin earLen, us i ≠ Sum.inr (Sum.inr r) := hear.1
    have hno_earR : ∀ j : Fin (a + 2), ∀ r : Fin earLen, vs j ≠ Sum.inr (Sum.inr r) := hear.2
    have hmid_nbrsL : ∀ (e : GenEdge G) (r : Fin (s e)),
        G2 G s earLen uStar vStar (Sum.inr (Sum.inl ⟨e, r⟩)) =
          {Sum.inr (Sum.inl ⟨e, r⟩),
            if h : r.val + 1 < s e then Sum.inr (Sum.inl ⟨e, ⟨r.val + 1, h⟩⟩) else Sum.inl e.1.2} := by
      intro e r; ext y; rw [mem_G2_iff]
      rcases y with v | ⟨e', r'⟩ | r'
      · simp only [adj2Prop, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl, hr⟩; right; simp [show ¬ (r.val + 1 < s e) by omega]
        · rintro (h | h); · simp at h
          · split_ifs at h with hlt
            injection h with hv; exact ⟨hv, by omega⟩
      · simp only [adj2Prop, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl, h1 | h2⟩
          · left; congr 2; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext h1.symm
          · right; have hlt : r.val + 1 < s e := by omega
            simp only [hlt, ↓reduceDIte]; congr 2; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext h2.symm
        · rintro (h | h)
          · injection h with h1; injection h1 with h2; rcases Sigma.mk.inj h2 with ⟨rfl, hr⟩
            exact ⟨rfl, Or.inl (congrArg Fin.val (eq_of_heq hr)).symm⟩
          · split_ifs at h with hlt
            injection h with h1; injection h1 with h2; rcases Sigma.mk.inj h2 with ⟨rfl, hr⟩
            exact ⟨rfl, Or.inr (congrArg Fin.val (eq_of_heq hr)).symm⟩
      · simp only [adj2Prop, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro h; exact False.elim h
        · rintro (h | h); · simp at h
          · split_ifs at h <;> simp at h
    have hmid_nbrsR : ∀ (e : GenEdge G) (r : Fin (s e)),
        gRightNbrs (G2 G s earLen uStar vStar) (Sum.inr (Sum.inl ⟨e, r⟩)) =
          {Sum.inr (Sum.inl ⟨e, r⟩),
            if h : 0 < r.val then Sum.inr (Sum.inl ⟨e, ⟨r.val - 1, by omega⟩⟩) else Sum.inl e.1.1} := by
      intro e r; ext x; simp only [gRightNbrs, Finset.mem_filter, Finset.mem_univ, true_and, mem_G2_iff]
      rcases x with u | ⟨e', r'⟩ | r'
      · simp only [adj2Prop, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl, hr0⟩; right; simp [show ¬ (0 < r.val) by omega]
        · rintro (h | h); · simp at h
          · split_ifs at h with hpos
            injection h with hu; exact ⟨hu, by omega⟩
      · simp only [adj2Prop, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl, h1 | h2⟩
          · left; congr 2; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext h1
          · right; have hpos : 0 < r.val := by omega
            simp only [hpos, ↓reduceDIte]; congr 2; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext (by (try dsimp); omega)
        · rintro (h | h)
          · injection h with h1; injection h1 with h2; rcases Sigma.mk.inj h2 with ⟨rfl, hr⟩
            exact ⟨rfl, Or.inl (congrArg Fin.val (eq_of_heq hr))⟩
          · split_ifs at h with hpos
            injection h with h1; injection h1 with h2; rcases Sigma.mk.inj h2 with ⟨rfl, hr⟩
            have hv := congrArg Fin.val (eq_of_heq hr); exact ⟨rfl, Or.inr (by dsimp at hv; omega)⟩
      · simp only [adj2Prop, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro h; exact False.elim h
        · rintro (h | h); · simp at h
          · split_ifs at h <;> simp at h
    have hmid_full : ∀ (e : GenEdge G),
        (∃ r : Fin (s e), (∃ i, us i = Sum.inr (Sum.inl ⟨e, r⟩)) ∨ (∃ j, vs j = Sum.inr (Sum.inl ⟨e, r⟩))) →
        (∀ r : Fin (s e), ∃ i, us i = Sum.inr (Sum.inl ⟨e, r⟩)) ∧
        (∃ i, us i = Sum.inl e.1.1) ∧ (∃ j, vs j = Sum.inl e.1.2) := by
      intro e hsome
      have hL_from_R : ∀ r : Fin (s e), (∃ j, vs j = Sum.inr (Sum.inl ⟨e, r⟩)) →
          ∃ i, us i = Sum.inr (Sum.inl ⟨e, r⟩) := by
        intro r hr
        have hne : (Sum.inr (Sum.inl ⟨e, r⟩) : L2 G s earLen) ≠
            (if h : 0 < r.val then Sum.inr (Sum.inl ⟨e, ⟨r.val - 1, by omega⟩⟩) else Sum.inl e.1.1) := by
          split_ifs with h
          · intro heq; injection heq with h1; injection h1 with h2
            have hv := congrArg Fin.val (eq_of_heq (Sigma.mk.inj h2).2); dsimp at hv; omega
          · simp
        exact (hdeg2_prop_R _ _ _ hne (hmid_nbrsR e r) hr).1
      have hsomeL : ∃ r0 : Fin (s e), ∃ i, us i = Sum.inr (Sum.inl ⟨e, r0⟩) := by
        rcases hsome with ⟨r, hL | hR⟩
        · exact ⟨r, hL⟩
        · exact ⟨r, hL_from_R r hR⟩
      rcases hsomeL with ⟨r0, i0, hi0⟩
      have hse_pos : 0 < s e := hse1 e
      have hstep_up : ∀ r : Fin (s e), (h : r.val + 1 < s e) →
          (∃ i, us i = Sum.inr (Sum.inl ⟨e, r⟩)) → ∃ i, us i = Sum.inr (Sum.inl ⟨e, ⟨r.val + 1, h⟩⟩) := by
        intro r h hr
        have hne : (Sum.inr (Sum.inl ⟨e, r⟩) : R2 G s earLen) ≠
            (if h' : r.val + 1 < s e then Sum.inr (Sum.inl ⟨e, ⟨r.val + 1, h'⟩⟩) else Sum.inl e.1.2) := by
          simp only [h, ↓reduceDIte]
          intro heq; injection heq with h1; injection h1 with h2
          have hv := congrArg Fin.val (eq_of_heq (Sigma.mk.inj h2).2); dsimp at hv; omega
        have hR := (hdeg2_prop_L _ _ _ hne (hmid_nbrsL e r) hr).2
        simp only [h, ↓reduceDIte] at hR
        exact hL_from_R ⟨r.val + 1, h⟩ hR
      have hstep_dn : ∀ r : Fin (s e), (h : 0 < r.val) →
          (∃ i, us i = Sum.inr (Sum.inl ⟨e, r⟩)) → ∃ i, us i = Sum.inr (Sum.inl ⟨e, ⟨r.val - 1, by omega⟩⟩) := by
        intro r h hr
        have hne1 : (Sum.inr (Sum.inl ⟨e, r⟩) : R2 G s earLen) ≠
            (if h' : r.val + 1 < s e then Sum.inr (Sum.inl ⟨e, ⟨r.val + 1, h'⟩⟩) else Sum.inl e.1.2) := by
          split_ifs with h'
          · intro heq; injection heq with h1; injection h1 with h2
            have hv := congrArg Fin.val (eq_of_heq (Sigma.mk.inj h2).2); dsimp at hv; omega
          · simp
        have hR := (hdeg2_prop_L _ _ _ hne1 (hmid_nbrsL e r) hr).1
        have hne2 : (Sum.inr (Sum.inl ⟨e, r⟩) : L2 G s earLen) ≠
            (if h' : 0 < r.val then Sum.inr (Sum.inl ⟨e, ⟨r.val - 1, by omega⟩⟩) else Sum.inl e.1.1) := by
          simp only [h, ↓reduceDIte]
          intro heq; injection heq with h1; injection h1 with h2
          have hv := congrArg Fin.val (eq_of_heq (Sigma.mk.inj h2).2); dsimp at hv; omega
        have hL := (hdeg2_prop_R _ _ _ hne2 (hmid_nbrsR e r) hR).2
        simp only [h, ↓reduceDIte] at hL
        exact hL
      have hall : ∀ r : Fin (s e), ∃ i, us i = Sum.inr (Sum.inl ⟨e, r⟩) := by
        have h0 : ∃ i, us i = Sum.inr (Sum.inl ⟨e, ⟨0, hse_pos⟩⟩) := by
          have hdn : ∀ d : ℕ, d ≤ r0.val → ∃ i, us i = Sum.inr (Sum.inl ⟨e, ⟨r0.val - d, by omega⟩⟩) := by
            intro d
            induction d with
            | zero => intro _; simpa using ⟨i0, hi0⟩
            | succ d ih =>
              intro hd
              have h := hstep_dn ⟨r0.val - d, by omega⟩ (by (try dsimp); omega) (ih (by omega))
              simpa [Nat.sub_sub] using h
          simpa using hdn r0.val le_rfl
        rintro ⟨r, hr⟩
        induction r with
        | zero => exact h0
        | succ r ih => exact hstep_up ⟨r, by omega⟩ hr (ih (by omega))
      refine ⟨hall, ?_, ?_⟩
      · have h0 := hall ⟨0, hse_pos⟩
        have hne1 : (Sum.inr (Sum.inl ⟨e, ⟨0, hse_pos⟩⟩) : R2 G s earLen) ≠
            (if h' : 0 + 1 < s e then Sum.inr (Sum.inl ⟨e, ⟨0 + 1, h'⟩⟩) else Sum.inl e.1.2) := by
          split_ifs with h'
          · intro heq; injection heq with h1; injection h1 with h2
            have hv := congrArg Fin.val (eq_of_heq (Sigma.mk.inj h2).2); dsimp at hv; omega
          · simp
        have hR0 := (hdeg2_prop_L _ _ _ hne1 (hmid_nbrsL e ⟨0, hse_pos⟩) h0).1
        have hne2 : (Sum.inr (Sum.inl ⟨e, ⟨0, hse_pos⟩⟩) : L2 G s earLen) ≠
            (if h' : 0 < (⟨0, hse_pos⟩ : Fin (s e)).val then
              Sum.inr (Sum.inl ⟨e, ⟨0 - 1, by omega⟩⟩) else Sum.inl e.1.1) := by simp
        have hL0 := (hdeg2_prop_R _ _ _ hne2 (hmid_nbrsR e ⟨0, hse_pos⟩) hR0).2
        simpa using hL0
      · have hlast := hall ⟨s e - 1, by omega⟩
        have hne1 : (Sum.inr (Sum.inl ⟨e, ⟨s e - 1, by omega⟩⟩) : R2 G s earLen) ≠
            (if h' : (s e - 1) + 1 < s e then Sum.inr (Sum.inl ⟨e, ⟨(s e - 1) + 1, h'⟩⟩) else Sum.inl e.1.2) := by
          simp [show ¬ ((s e - 1) + 1 < s e) by omega]
        have hRend := (hdeg2_prop_L _ _ _ hne1 (hmid_nbrsL e ⟨s e - 1, by omega⟩) hlast).2
        simpa [show ¬ ((s e - 1) + 1 < s e) by omega] using hRend
    let baseL : Finset (Fin (a + 2)) := Finset.univ.filter (fun i => (us i).isLeft)
    let baseR : Finset (Fin (a + 2)) := Finset.univ.filter (fun j => (vs j).isLeft)
    have hbaseL_ne : baseL.Nonempty := by
      cases hu0 : us 0 with
      | inl u => exact ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hu0]⟩⟩
      | inr z =>
        cases z with
        | inl er =>
          rcases (hmid_full er.1 ⟨er.2, Or.inl ⟨0, hu0⟩⟩).2.1 with ⟨i, hi⟩
          exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hi]⟩⟩
        | inr r => exact absurd hu0 (hno_earL 0 r)
    have hbaseR_ne : baseR.Nonempty := by
      cases hu0 : us 0 with
      | inl u =>
        have h1 := (mem_G2_iff G s earLen uStar vStar _ _).mp (hcyc 0).1
        rw [hu0] at h1
        cases hv0 : vs 0 with
        | inl v => exact ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hv0]⟩⟩
        | inr z =>
          cases z with
          | inl er =>
            rcases (hmid_full er.1 ⟨er.2, Or.inr ⟨0, hv0⟩⟩).2.2 with ⟨j, hj⟩
            exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hj]⟩⟩
          | inr r => exact absurd hv0 (hno_earR 0 r)
      | inr z =>
        cases z with
        | inl er =>
          rcases (hmid_full er.1 ⟨er.2, Or.inl ⟨0, hu0⟩⟩).2.2 with ⟨j, hj⟩
          exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hj]⟩⟩
        | inr r => exact absurd hu0 (hno_earL 0 r)
    let M := 2 * (a + 2)
    haveI : NeZero M := ⟨by omega⟩
    let w : Fin M → L2 G s earLen ⊕ R2 G s earLen := fun r =>
      if r.val % 2 = 0 then Sum.inl (us ⟨r.val / 2, by omega⟩)
      else Sum.inr (vs ⟨r.val / 2, by omega⟩)
    let isBase : L2 G s earLen ⊕ R2 G s earLen → Bool := fun z =>
      match z with
      | Sum.inl (Sum.inl _) => true
      | Sum.inr (Sum.inl _) => true
      | _ => false
    let Sbase : Finset (Fin M) := Finset.univ.filter (fun r => isBase (w r) = true)
    have hSbase_ne : Sbase.Nonempty := by
      rcases hbaseL_ne with ⟨i, hi⟩
      refine ⟨⟨2 * i.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
      have hisL := (Finset.mem_filter.mp hi).2
      have hmod : (2 * i.val) % 2 = 0 := by omega
      have hdiv : (⟨(2 * i.val) / 2, by omega⟩ : Fin (a + 2)) = i := Fin.ext (by (try dsimp); omega)
      simp only [w, hmod, ↓reduceIte, hdiv]
      cases hu : us i with
      | inl _ => rfl
      | inr _ => simp [hu] at hisL
    let edgeOf : L2 G s earLen ⊕ R2 G s earLen → Option (GenEdge G) := fun z =>
      match z with
      | Sum.inl (Sum.inr (Sum.inl ⟨e, _⟩)) => some e
      | Sum.inr (Sum.inr (Sum.inl ⟨e, _⟩)) => some e
      | _ => none
    have hw_adj : ∀ r : Fin M,
        (match w r, w (r + 1) with
         | Sum.inl l, Sum.inr r' => adj2Prop G s earLen uStar vStar l r'
         | Sum.inr r', Sum.inl l => adj2Prop G s earLen uStar vStar l r'
         | _, _ => False) := by
      intro r
      have hrm : (r + 1).val = (r.val + 1) % M := by simp [Fin.val_add, Fin.val_one']
      by_cases h0 : r.val % 2 = 0
      · have hlt : r.val + 1 < M := by omega
        have h1 : (r + 1).val = r.val + 1 := by rw [hrm, Nat.mod_eq_of_lt hlt]
        have hdiv : (r + 1).val / 2 = r.val / 2 := by omega
        have hmod : (r + 1).val % 2 ≠ 0 := by omega
        simp only [w, h0, ↓reduceIte, hmod]
        have hidx : (⟨(r + 1).val / 2, by omega⟩ : Fin (a + 2)) = ⟨r.val / 2, by omega⟩ := Fin.ext hdiv
        rw [hidx]
        exact (mem_G2_iff G s earLen uStar vStar _ _).mp (hcyc ⟨r.val / 2, by omega⟩).1
      · have hmod : (r + 1).val % 2 = 0 := by
          rw [hrm]
          by_cases hlt : r.val + 1 < M
          · rw [Nat.mod_eq_of_lt hlt]; omega
          · have : r.val + 1 = M := by omega
            rw [this, Nat.mod_self]
        simp only [w, h0, ↓reduceIte, hmod]
        have hidx : (⟨(r + 1).val / 2, by have := (r + 1).isLt; omega⟩ : Fin (a + 2)) = ⟨r.val / 2, by omega⟩ + 1 := by
          apply Fin.ext; dsimp only; rw [hrm]
          by_cases hlt : r.val + 1 < M
          · rw [Nat.mod_eq_of_lt hlt]
            have : r.val / 2 + 1 < a + 2 := by omega
            simp [Fin.val_add, Fin.val_one, Nat.mod_eq_of_lt this]; omega
          · have hrval : r.val + 1 = M := by omega
            rw [hrval, Nat.mod_self]
            have : r.val / 2 + 1 = a + 2 := by omega
            simp [Fin.val_add, Fin.val_one, this]
        rw [hidx]
        exact (mem_G2_iff G s earLen uStar vStar _ _).mp (hcyc ⟨r.val / 2, by omega⟩).2
    have hno_ear_w : ∀ r : Fin M,
        (∀ x, w r ≠ Sum.inl (Sum.inr (Sum.inr x))) ∧ (∀ y, w r ≠ Sum.inr (Sum.inr (Sum.inr y))) := by
      intro r; dsimp only [w]; split_ifs
      · exact ⟨fun x h => hno_earL _ x (Sum.inl.inj h), fun _ h => (by cases h)⟩
      · exact ⟨fun _ h => (by cases h), fun y h => hno_earR _ y (Sum.inr.inj h)⟩
    have hstep_edge : ∀ r : Fin M, isBase (w r) = true →
        ∃ e : GenEdge G,
          edgeOf (w (r + 1)) = some e ∧
          ((w r = Sum.inl (Sum.inl e.1.1) ∧ w (r + 1) = Sum.inr (Sum.inr (Sum.inl ⟨e, ⟨0, hse1 e⟩⟩))) ∨
           (w r = Sum.inr (Sum.inl e.1.2) ∧ w (r + 1) = Sum.inl (Sum.inr (Sum.inl ⟨e, ⟨s e - 1, by have := hse1 e; omega⟩⟩)))) := by
      intro r hr
      have hadj := hw_adj r
      cases hwr : w r with
      | inl l =>
        cases l with
        | inl u =>
          cases hwr1 : w (r + 1) with
          | inl _ => rw [hwr, hwr1] at hadj; exact False.elim hadj
          | inr r' =>
            cases r' with
            | inl _ => rw [hwr, hwr1] at hadj; exact False.elim hadj
            | inr z =>
              cases z with
              | inl er =>
                rw [hwr, hwr1] at hadj
                rcases hadj with ⟨rfl, hr0⟩
                refine ⟨er.1, rfl, Or.inl ⟨rfl, ?_⟩⟩
                congr 3; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext hr0
              | inr x => exact absurd hwr1 ((hno_ear_w (r + 1)).2 x)
        | inr _ => rw [hwr] at hr; simp [isBase] at hr
      | inr r' =>
        cases r' with
        | inl v =>
          cases hwr1 : w (r + 1) with
          | inr _ => rw [hwr, hwr1] at hadj; exact False.elim hadj
          | inl l =>
            cases l with
            | inl _ => rw [hwr, hwr1] at hadj; exact False.elim hadj
            | inr z =>
              cases z with
              | inl er =>
                rw [hwr, hwr1] at hadj
                rcases hadj with ⟨rfl, hrend⟩
                refine ⟨er.1, rfl, Or.inr ⟨rfl, ?_⟩⟩
                congr 3; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext (by (try dsimp); omega)
              | inr x => exact absurd hwr1 ((hno_ear_w (r + 1)).1 x)
        | inr _ => rw [hwr] at hr; simp [isBase] at hr
    have hw_inj : Function.Injective w := by
      intro r1 r2 heq
      dsimp only [w] at heq
      by_cases h1 : r1.val % 2 = 0 <;> by_cases h2 : r2.val % 2 = 0
      · simp only [h1, h2, ↓reduceIte, Sum.inl.injEq] at heq
        have hdiv := congrArg Fin.val (us.injective heq); dsimp at hdiv; exact Fin.ext (by omega)
      · simp [h1, h2] at heq
      · simp [h1, h2] at heq
      · simp only [h1, h2, ↓reduceIte, Sum.inr.injEq] at heq
        have hdiv := congrArg Fin.val (vs.injective heq); dsimp at hdiv; exact Fin.ext (by omega)
    have hmid_traverse_fwd : ∀ (r : Fin M) (e : GenEdge G),
        w r = Sum.inl (Sum.inl e.1.1) →
        w (r + 1) = Sum.inr (Sum.inr (Sum.inl ⟨e, ⟨0, hse1 e⟩⟩)) →
        (∀ d : ℕ, d < 2 * s e →
          isBase (w (r + ⟨(d + 1) % M, Nat.mod_lt _ (by omega)⟩)) = false ∧
          edgeOf (w (r + ⟨(d + 1) % M, Nat.mod_lt _ (by omega)⟩)) = some e) ∧
        w (r + ⟨(2 * s e + 1) % M, Nat.mod_lt _ (by omega)⟩) = Sum.inr (Sum.inl e.1.2) ∧
        (∃ d < 2 * s e, w (r + ⟨(d + 1) % M, Nat.mod_lt _ (by omega)⟩) =
          Sum.inr (Sum.inr (Sum.inl ⟨e, ⟨0, hse1 e⟩⟩))) := by
      intro r e hwr hwr1
      have hwalk : ∀ d : ℕ, d ≤ 2 * s e →
          w (r + ⟨(d + 1) % M, Nat.mod_lt _ (by omega)⟩) =
            if hdlt : d < 2 * s e then
              if d % 2 = 0 then Sum.inr (Sum.inr (Sum.inl ⟨e, ⟨d / 2, by omega⟩⟩))
              else Sum.inl (Sum.inr (Sum.inl ⟨e, ⟨d / 2, by omega⟩⟩))
            else Sum.inr (Sum.inl e.1.2) := by
        intro d
        induction d using Nat.strong_induction_on with
        | ind d ih =>
          cases d with
          | zero =>
            intro _
            have h1 : (⟨(0 + 1) % M, Nat.mod_lt _ (by omega)⟩ : Fin M) = 1 := by
              apply Fin.ext; simp [Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < M)]
            rw [h1, hwr1]
            have hpos : 0 < 2 * s e := by have := hse1 e; omega
            simp [hpos]
          | succ d =>
            intro hd
            have hcur := ih d (by omega) (by omega)
            have hdlt : d < 2 * s e := by omega
            simp only [hdlt, ↓reduceDIte] at hcur
            have hidx_succ : r + ⟨(d + 1 + 1) % M, Nat.mod_lt _ (by omega)⟩ =
                (r + ⟨(d + 1) % M, Nat.mod_lt _ (by omega)⟩) + 1 := by
              apply Fin.ext
              simp only [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < M), Nat.add_mod_mod, Nat.mod_add_mod]
              congr 1
            have hprev_eq : (r + ⟨(d + 1) % M, Nat.mod_lt _ (by omega)⟩) - 1 =
                r + ⟨d % M, Nat.mod_lt _ (by omega)⟩ := by
              apply sub_eq_of_eq_add
              apply Fin.ext
              simp only [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < M), Nat.add_mod_mod, Nat.mod_add_mod]
              congr 1
            have hne_prev : w ((r + ⟨(d + 1) % M, Nat.mod_lt _ (by omega)⟩) + 1) ≠
                w (r + ⟨d % M, Nat.mod_lt _ (by omega)⟩) := by
              intro h
              have heq := hw_inj h
              rw [← hprev_eq] at heq
              exact fin_sub_one_ne_add_one (by omega : 3 ≤ M) _ heq.symm
            have hadj := hw_adj (r + ⟨(d + 1) % M, Nat.mod_lt _ (by omega)⟩)
            rw [hidx_succ]
            by_cases hd0 : d % 2 = 0
            · simp only [hd0, ↓reduceIte] at hcur
              rw [hcur] at hadj
              have hprev_val : w (r + ⟨d % M, Nat.mod_lt _ (by omega)⟩) =
                  if h0 : d = 0 then Sum.inl (Sum.inl e.1.1)
                  else Sum.inl (Sum.inr (Sum.inl ⟨e, ⟨d / 2 - 1, by omega⟩⟩)) := by
                by_cases h0 : d = 0
                · subst h0; simp [hwr]
                · simp only [h0, ↓reduceDIte]
                  have h_eq : d - 1 + 1 = d := by omega
                  have hprev2 := ih (d - 1) (by omega) (by omega)
                  rw [h_eq] at hprev2
                  have h1 : d - 1 < 2 * s e := by omega
                  have h2 : (d - 1) % 2 ≠ 0 := by omega
                  have h3 : (d - 1) / 2 = d / 2 - 1 := by omega
                  simp only [h1, h2, ↓reduceDIte, ↓reduceIte] at hprev2
                  rw [hprev2]; congr 3; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext h3
              have h_in_nbrs : ∃ x : L2 G s earLen, w ((r + ⟨(d + 1) % M, Nat.mod_lt _ (by omega)⟩) + 1) = Sum.inl x ∧
                  x ∈ gRightNbrs (G2 G s earLen uStar vStar) (Sum.inr (Sum.inl ⟨e, ⟨d / 2, by omega⟩⟩)) := by
                cases hnext : w ((r + ⟨(d + 1) % M, Nat.mod_lt _ (by omega)⟩) + 1) with
                | inr _ => rw [hnext] at hadj; exact False.elim hadj
                | inl x =>
                  rw [hnext] at hadj
                  exact ⟨x, rfl, (mem_gRightNbrs_iff _ _ _).mpr ((mem_G2_iff G s earLen uStar vStar _ _).mpr hadj)⟩
              rcases h_in_nbrs with ⟨x, hx_eq, hx_mem⟩
              rw [hmid_nbrsR e ⟨d / 2, by omega⟩, Finset.mem_insert, Finset.mem_singleton] at hx_mem
              rw [hx_eq] at hne_prev ⊢
              rcases hx_mem with rfl | rfl
              · have hlt2 : d + 1 < 2 * s e := by omega
                have hmod2 : (d + 1) % 2 ≠ 0 := by omega
                have hdiv2 : (d + 1) / 2 = d / 2 := by omega
                simp only [hlt2, hmod2, ↓reduceDIte, ↓reduceIte]
                congr 3; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext hdiv2.symm
              · exfalso; apply hne_prev; rw [hprev_val]
                by_cases h0 : d = 0
                · subst h0; simp
                · simp [h0, show 0 < d / 2 by omega]
            · simp only [hd0, ↓reduceIte] at hcur
              rw [hcur] at hadj
              have hprev_val : w (r + ⟨d % M, Nat.mod_lt _ (by omega)⟩) =
                  Sum.inr (Sum.inr (Sum.inl ⟨e, ⟨d / 2, by omega⟩⟩)) := by
                have h_eq : d - 1 + 1 = d := by omega
                have hprev2 := ih (d - 1) (by omega) (by omega)
                rw [h_eq] at hprev2
                have h1 : d - 1 < 2 * s e := by omega
                have h2 : (d - 1) % 2 = 0 := by omega
                have h3 : (d - 1) / 2 = d / 2 := by omega
                simp only [h1, h2, ↓reduceDIte, ↓reduceIte] at hprev2
                rw [hprev2]; congr 3; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext h3
              have h_in_nbrs : ∃ y : R2 G s earLen, w ((r + ⟨(d + 1) % M, Nat.mod_lt _ (by omega)⟩) + 1) = Sum.inr y ∧
                  y ∈ G2 G s earLen uStar vStar (Sum.inr (Sum.inl ⟨e, ⟨d / 2, by omega⟩⟩)) := by
                cases hnext : w ((r + ⟨(d + 1) % M, Nat.mod_lt _ (by omega)⟩) + 1) with
                | inl _ => rw [hnext] at hadj; exact False.elim hadj
                | inr y =>
                  rw [hnext] at hadj
                  exact ⟨y, rfl, (mem_G2_iff G s earLen uStar vStar _ _).mpr hadj⟩
              rcases h_in_nbrs with ⟨y, hy_eq, hy_mem⟩
              rw [hmid_nbrsL e ⟨d / 2, by omega⟩, Finset.mem_insert, Finset.mem_singleton] at hy_mem
              rw [hy_eq] at hne_prev ⊢
              rcases hy_mem with rfl | rfl
              · exact absurd hprev_val.symm hne_prev
              · by_cases hlt2 : d + 1 < 2 * s e
                · have hlt3 : d / 2 + 1 < s e := by omega
                  have hmod2 : (d + 1) % 2 = 0 := by omega
                  have hdiv2 : (d + 1) / 2 = d / 2 + 1 := by omega
                  simp only [hlt2, hlt3, hmod2, ↓reduceDIte, ↓reduceIte]
                  congr 3; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext hdiv2.symm
                · have hnot3 : ¬ (d / 2 + 1 < s e) := by omega
                  simp [hlt2, hnot3]
      refine ⟨fun d hd => ?_, ?_, ?_⟩
      · have h := hwalk d (by omega)
        simp only [hd, ↓reduceDIte] at h
        split_ifs at h <;> rw [h] <;> simp [isBase, edgeOf]
      · have h := hwalk (2 * s e) le_rfl
        simp only [lt_irrefl, ↓reduceDIte] at h
        exact h
      · refine ⟨0, by have := hse1 e; omega, ?_⟩
        have h := hwalk 0 (by omega)
        have hpos : 0 < 2 * s e := by have := hse1 e; omega
        simp only [hpos, ↓reduceDIte] at h
        exact h
    have hmid_traverse_bwd : ∀ (r : Fin M) (e : GenEdge G),
        w r = Sum.inr (Sum.inl e.1.2) →
        w (r + 1) = Sum.inl (Sum.inr (Sum.inl ⟨e, ⟨s e - 1, by have := hse1 e; omega⟩⟩)) →
        (∀ d : ℕ, d < 2 * s e →
          isBase (w (r + ⟨(d + 1) % M, Nat.mod_lt _ (by omega)⟩)) = false ∧
          edgeOf (w (r + ⟨(d + 1) % M, Nat.mod_lt _ (by omega)⟩)) = some e) ∧
        w (r + ⟨(2 * s e + 1) % M, Nat.mod_lt _ (by omega)⟩) = Sum.inl (Sum.inl e.1.1) ∧
        (∃ d < 2 * s e, w (r + ⟨(d + 1) % M, Nat.mod_lt _ (by omega)⟩) =
          Sum.inr (Sum.inr (Sum.inl ⟨e, ⟨0, hse1 e⟩⟩))) := by
      intro r e hwr hwr1
      have hwalk : ∀ d : ℕ, d ≤ 2 * s e →
          w (r + ⟨(d + 1) % M, Nat.mod_lt _ (by omega)⟩) =
            if hdlt : d < 2 * s e then
              if d % 2 = 0 then Sum.inl (Sum.inr (Sum.inl ⟨e, ⟨s e - 1 - d / 2, by omega⟩⟩))
              else Sum.inr (Sum.inr (Sum.inl ⟨e, ⟨s e - 1 - d / 2, by omega⟩⟩))
            else Sum.inl (Sum.inl e.1.1) := by
        intro d
        induction d using Nat.strong_induction_on with
        | ind d ih =>
          cases d with
          | zero =>
            intro _
            have h1 : (⟨(0 + 1) % M, Nat.mod_lt _ (by omega)⟩ : Fin M) = 1 := by
              apply Fin.ext; simp [Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < M)]
            rw [h1, hwr1]
            have hpos : 0 < 2 * s e := by have := hse1 e; omega
            simp [hpos]
          | succ d =>
            intro hd
            have hcur := ih d (by omega) (by omega)
            have hdlt : d < 2 * s e := by omega
            simp only [hdlt, ↓reduceDIte] at hcur
            have hidx_succ : r + ⟨(d + 1 + 1) % M, Nat.mod_lt _ (by omega)⟩ =
                (r + ⟨(d + 1) % M, Nat.mod_lt _ (by omega)⟩) + 1 := by
              apply Fin.ext
              simp only [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < M), Nat.add_mod_mod, Nat.mod_add_mod]
              congr 1
            have hprev_eq : (r + ⟨(d + 1) % M, Nat.mod_lt _ (by omega)⟩) - 1 =
                r + ⟨d % M, Nat.mod_lt _ (by omega)⟩ := by
              apply sub_eq_of_eq_add
              apply Fin.ext
              simp only [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < M), Nat.add_mod_mod, Nat.mod_add_mod]
              congr 1
            have hne_prev : w ((r + ⟨(d + 1) % M, Nat.mod_lt _ (by omega)⟩) + 1) ≠
                w (r + ⟨d % M, Nat.mod_lt _ (by omega)⟩) := by
              intro h
              have heq := hw_inj h
              rw [← hprev_eq] at heq
              exact fin_sub_one_ne_add_one (by omega : 3 ≤ M) _ heq.symm
            have hadj := hw_adj (r + ⟨(d + 1) % M, Nat.mod_lt _ (by omega)⟩)
            rw [hidx_succ]
            by_cases hd0 : d % 2 = 0
            · simp only [hd0, ↓reduceIte] at hcur
              rw [hcur] at hadj
              have hprev_val : w (r + ⟨d % M, Nat.mod_lt _ (by omega)⟩) =
                  if h0 : d = 0 then Sum.inr (Sum.inl e.1.2)
                  else Sum.inr (Sum.inr (Sum.inl ⟨e, ⟨s e - 1 - d / 2 + 1, by omega⟩⟩)) := by
                by_cases h0 : d = 0
                · subst h0; simp [hwr]
                · simp only [h0, ↓reduceDIte]
                  have h_eq : d - 1 + 1 = d := by omega
                  have hprev2 := ih (d - 1) (by omega) (by omega)
                  rw [h_eq] at hprev2
                  have h1 : d - 1 < 2 * s e := by omega
                  have h2 : (d - 1) % 2 ≠ 0 := by omega
                  have h3 : s e - 1 - (d - 1) / 2 = s e - 1 - d / 2 + 1 := by omega
                  simp only [h1, h2, ↓reduceDIte, ↓reduceIte] at hprev2
                  rw [hprev2]; congr 3; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext h3
              have h_in_nbrs : ∃ y : R2 G s earLen, w ((r + ⟨(d + 1) % M, Nat.mod_lt _ (by omega)⟩) + 1) = Sum.inr y ∧
                  y ∈ G2 G s earLen uStar vStar (Sum.inr (Sum.inl ⟨e, ⟨s e - 1 - d / 2, by omega⟩⟩)) := by
                cases hnext : w ((r + ⟨(d + 1) % M, Nat.mod_lt _ (by omega)⟩) + 1) with
                | inl _ => rw [hnext] at hadj; exact False.elim hadj
                | inr y =>
                  rw [hnext] at hadj
                  exact ⟨y, rfl, (mem_G2_iff G s earLen uStar vStar _ _).mpr hadj⟩
              rcases h_in_nbrs with ⟨y, hy_eq, hy_mem⟩
              rw [hmid_nbrsL e ⟨s e - 1 - d / 2, by omega⟩, Finset.mem_insert, Finset.mem_singleton] at hy_mem
              rw [hy_eq] at hne_prev ⊢
              rcases hy_mem with rfl | rfl
              · have hlt2 : d + 1 < 2 * s e := by omega
                have hmod2 : (d + 1) % 2 ≠ 0 := by omega
                have hdiv2 : s e - 1 - (d + 1) / 2 = s e - 1 - d / 2 := by omega
                simp only [hlt2, hmod2, ↓reduceDIte, ↓reduceIte]
                congr 3; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext hdiv2.symm
              · exfalso; apply hne_prev; rw [hprev_val]
                by_cases h0 : d = 0
                · subst h0; simp [show ¬ (s e - 1 + 1 < s e) by have := hse1 e; omega]
                · simp [h0, show s e - 1 - d / 2 + 1 < s e by omega]
            · simp only [hd0, ↓reduceIte] at hcur
              rw [hcur] at hadj
              have hprev_val : w (r + ⟨d % M, Nat.mod_lt _ (by omega)⟩) =
                  Sum.inl (Sum.inr (Sum.inl ⟨e, ⟨s e - 1 - d / 2, by omega⟩⟩)) := by
                have h_eq : d - 1 + 1 = d := by omega
                have hprev2 := ih (d - 1) (by omega) (by omega)
                rw [h_eq] at hprev2
                have h1 : d - 1 < 2 * s e := by omega
                have h2 : (d - 1) % 2 = 0 := by omega
                have h3 : (d - 1) / 2 = d / 2 := by omega
                simp only [h1, h2, ↓reduceDIte, ↓reduceIte] at hprev2
                rw [hprev2]; congr 3; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext (by (try dsimp); omega)
              have h_in_nbrs : ∃ x : L2 G s earLen, w ((r + ⟨(d + 1) % M, Nat.mod_lt _ (by omega)⟩) + 1) = Sum.inl x ∧
                  x ∈ gRightNbrs (G2 G s earLen uStar vStar) (Sum.inr (Sum.inl ⟨e, ⟨s e - 1 - d / 2, by omega⟩⟩)) := by
                cases hnext : w ((r + ⟨(d + 1) % M, Nat.mod_lt _ (by omega)⟩) + 1) with
                | inr _ => rw [hnext] at hadj; exact False.elim hadj
                | inl x =>
                  rw [hnext] at hadj
                  exact ⟨x, rfl, (mem_gRightNbrs_iff _ _ _).mpr ((mem_G2_iff G s earLen uStar vStar _ _).mpr hadj)⟩
              rcases h_in_nbrs with ⟨x, hx_eq, hx_mem⟩
              rw [hmid_nbrsR e ⟨s e - 1 - d / 2, by omega⟩, Finset.mem_insert, Finset.mem_singleton] at hx_mem
              rw [hx_eq] at hne_prev ⊢
              rcases hx_mem with rfl | rfl
              · exact absurd hprev_val.symm hne_prev
              · by_cases hlt2 : d + 1 < 2 * s e
                · have hpos : 0 < s e - 1 - d / 2 := by omega
                  have hmod2 : (d + 1) % 2 = 0 := by omega
                  have hdiv2 : s e - 1 - (d + 1) / 2 = s e - 1 - d / 2 - 1 := by omega
                  simp only [hlt2, hpos, hmod2, ↓reduceDIte, ↓reduceIte]
                  congr 3; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext hdiv2.symm
                · have hnotpos : ¬ (0 < s e - 1 - d / 2) := by omega
                  simp [hlt2, hnotpos]
      refine ⟨fun d hd => ?_, ?_, ?_⟩
      · have h := hwalk d (by omega)
        simp only [hd, ↓reduceDIte] at h
        split_ifs at h <;> rw [h] <;> simp [isBase, edgeOf]
      · have h := hwalk (2 * s e) le_rfl
        simp only [lt_irrefl, ↓reduceDIte] at h
        exact h
      · refine ⟨2 * s e - 1, by have := hse1 e; omega, ?_⟩
        have h := hwalk (2 * s e - 1) (by omega)
        have hlt : 2 * s e - 1 < 2 * s e := by have := hse1 e; omega
        have hodd : (2 * s e - 1) % 2 ≠ 0 := by have := hse1 e; omega
        simp only [hlt, hodd, ↓reduceDIte, ↓reduceIte] at h
        rw [h]
        congr 3; refine Sigma.ext rfl (heq_of_eq ?_); apply Fin.ext
        have := hse1 e; dsimp; omega
    let mTot := Sbase.card
    have hmTot_pos : 0 < mTot := Finset.card_pos.mpr hSbase_ne
    haveI : NeZero mTot := ⟨by omega⟩
    let ord : Fin mTot ≃o Sbase := Sbase.orderIsoOfFin rfl
    let idx : Fin mTot → Fin M := fun i => (ord i).1
    have hidx_base : ∀ i : Fin mTot, isBase (w (idx i)) = true := fun i =>
      (Finset.mem_filter.mp (ord i).2).2
    have hidx_mono : StrictMono idx := fun a b hab => ord.strictMono hab
    have hnext_base : ∀ i : Fin mTot, ∃ e : GenEdge G,
        ((w (idx i) = Sum.inl (Sum.inl e.1.1) ∧ w (idx (i + 1)) = Sum.inr (Sum.inl e.1.2)) ∨
         (w (idx i) = Sum.inr (Sum.inl e.1.2) ∧ w (idx (i + 1)) = Sum.inl (Sum.inl e.1.1))) ∧
        (∃ d < 2 * s e, w (idx i + ⟨(d + 1) % M, Nat.mod_lt _ (by omega)⟩) =
          Sum.inr (Sum.inr (Sum.inl ⟨e, ⟨0, hse1 e⟩⟩))) ∧
        ((idx (i + 1)).val + M - (idx i).val) % M = 2 * s e + 1 ∧
        idx (i + 1) = idx i + ⟨(2 * s e + 1) % M, Nat.mod_lt _ (by omega)⟩ ∧
        2 * s e + 1 < M := by
      intro i
      rcases hstep_edge (idx i) (hidx_base i) with ⟨e, _, hdir⟩
      have htrav : (∀ d : ℕ, d < 2 * s e →
            isBase (w (idx i + ⟨(d + 1) % M, Nat.mod_lt _ (by omega)⟩)) = false ∧
            edgeOf (w (idx i + ⟨(d + 1) % M, Nat.mod_lt _ (by omega)⟩)) = some e) ∧
          (((w (idx i) = Sum.inl (Sum.inl e.1.1) ∧
            w (idx i + ⟨(2 * s e + 1) % M, Nat.mod_lt _ (by omega)⟩) = Sum.inr (Sum.inl e.1.2)) ∨
           (w (idx i) = Sum.inr (Sum.inl e.1.2) ∧
            w (idx i + ⟨(2 * s e + 1) % M, Nat.mod_lt _ (by omega)⟩) = Sum.inl (Sum.inl e.1.1))) ∧
          (∃ d < 2 * s e, w (idx i + ⟨(d + 1) % M, Nat.mod_lt _ (by omega)⟩) =
            Sum.inr (Sum.inr (Sum.inl ⟨e, ⟨0, hse1 e⟩⟩)))) := by
        rcases hdir with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rcases hmid_traverse_fwd (idx i) e h1 h2 with ⟨ha, hb, hc⟩
          exact ⟨ha, Or.inl ⟨h1, hb⟩, hc⟩
        · rcases hmid_traverse_bwd (idx i) e h1 h2 with ⟨ha, hb, hc⟩
          exact ⟨ha, Or.inr ⟨h1, hb⟩, hc⟩
      let dest : Fin M := idx i + ⟨(2 * s e + 1) % M, Nat.mod_lt _ (by omega)⟩
      have hdest_base : isBase (w dest) = true := by
        rcases htrav.2.1 with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [dest, h, isBase]
      have hdest_ne : dest ≠ idx i := by
        intro heq
        rcases htrav.2.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> (change w dest = _ at h2; rw [heq] at h2; rw [h1] at h2; cases h2)
      have h2se_lt : 2 * s e + 1 < M := by
        by_contra hge
        have hlt : M - 1 < 2 * s e := by omega
        have hdest_in : ∃ d < 2 * s e, idx i + ⟨(d + 1) % M, Nat.mod_lt _ (by omega)⟩ = idx i := by
          refine ⟨M - 1, hlt, ?_⟩
          have : (M - 1 + 1) % M = 0 := by rw [show M - 1 + 1 = M by omega, Nat.mod_self]
          simp [this]
        rcases hdest_in with ⟨d, hd, heq⟩
        have hf := (htrav.1 d hd).1
        rw [heq, hidx_base i] at hf
        cases hf
      have hdest_eq : idx (i + 1) = dest := by
        have hdest_inS : dest ∈ Sbase := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdest_base⟩
        let tdest : Fin mTot := ord.symm ⟨dest, hdest_inS⟩
        have htdest_eq : idx tdest = dest := by
          dsimp only [idx, tdest]
          exact congrArg Subtype.val (ord.apply_symm_apply _)
        have hgap_ne : ∀ r' ∈ Sbase, ∀ d : ℕ, d < 2 * s e →
            r' ≠ idx i + ⟨(d + 1) % M, Nat.mod_lt _ (by omega)⟩ := by
          intro r' hr' d hd heq
          have hb := (Finset.mem_filter.mp hr').2
          rw [heq, (htrav.1 d hd).1] at hb; cases hb
        have hno_between : ∀ j : Fin mTot, ((idx j).val + M - (idx i).val) % M = 0 ∨
            2 * s e + 1 ≤ ((idx j).val + M - (idx i).val) % M := by
          intro j
          by_cases h0 : ((idx j).val + M - (idx i).val) % M = 0
          · left; exact h0
          · right
            by_contra hlt
            have hd : ((idx j).val + M - (idx i).val) % M - 1 < 2 * s e := by omega
            apply hgap_ne (idx j) (ord j).2 (((idx j).val + M - (idx i).val) % M - 1) hd
            apply Fin.ext
            simp only [Fin.val_add]
            have h1 : ((idx j).val + M - (idx i).val) % M - 1 + 1 = ((idx j).val + M - (idx i).val) % M := by omega
            rw [h1, Nat.mod_mod, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
            have h2 : (idx i).val + ((idx j).val + M - (idx i).val) = (idx j).val + M := by
              have := (idx i).isLt; omega
            rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt (idx j).isLt]
        have hdist_dest : (dest.val + M - (idx i).val) % M = 2 * s e + 1 := by
          have hdv : dest.val = ((idx i).val + (2 * s e + 1)) % M := by
            simp [dest, Fin.val_add, Nat.mod_eq_of_lt h2se_lt]
          rw [hdv]
          by_cases hlt : (idx i).val + (2 * s e + 1) < M
          · rw [Nat.mod_eq_of_lt hlt]
            have : (idx i).val + (2 * s e + 1) + M - (idx i).val = (2 * s e + 1) + M := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt h2se_lt]
          · have hlt2 : (idx i).val + (2 * s e + 1) - M < M := by have := (idx i).isLt; omega
            have hgeM : M ≤ (idx i).val + (2 * s e + 1) := by omega
            rw [Nat.mod_eq_sub_mod hgeM, Nat.mod_eq_of_lt hlt2]
            have : (idx i).val + (2 * s e + 1) - M + M - (idx i).val = 2 * s e + 1 := by omega
            rw [this, Nat.mod_eq_of_lt h2se_lt]
        have hsucc_eq : i + 1 = tdest := by
          by_contra hne
          have hdist_next := hno_between (i + 1)
          have hne_i : i + 1 ≠ i := by
            intro h
            by_cases hm1 : mTot = 1
            · have hti : tdest = i := Fin.ext (by have := tdest.isLt; have := i.isLt; omega)
              exact hdest_ne (by rw [← htdest_eq, hti])
            · exact fin_add_one_ne_self (by omega) i h
          have hdist_pos : ((idx (i + 1)).val + M - (idx i).val) % M ≠ 0 := by
            intro h0
            have heq : idx (i + 1) = idx i := by
              apply Fin.ext
              by_cases hle : (idx i).val ≤ (idx (i + 1)).val
              · have : (idx (i + 1)).val + M - (idx i).val = ((idx (i + 1)).val - (idx i).val) + M := by omega
                rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := (idx (i + 1)).isLt; omega)] at h0
                omega
              · rw [Nat.mod_eq_of_lt (by have := (idx (i + 1)).isLt; omega)] at h0; omega
            exact hne_i (hidx_mono.injective heq)
          have hge_next : 2 * s e + 1 ≤ ((idx (i + 1)).val + M - (idx i).val) % M :=
            hdist_next.resolve_left hdist_pos
          by_cases hwrap : i.val + 1 < mTot
          · have hlt_next : (idx i).val < (idx (i + 1)).val := by
              apply hidx_mono; change i.val < (i + 1).val
              rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < mTot), Nat.mod_eq_of_lt hwrap]; omega
            have hd_next : ((idx (i + 1)).val + M - (idx i).val) % M = (idx (i + 1)).val - (idx i).val := by
              have : (idx (i + 1)).val + M - (idx i).val = ((idx (i + 1)).val - (idx i).val) + M := by omega
              rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := (idx (i + 1)).isLt; omega)]
            rw [hd_next] at hge_next
            have hdv_lt : (idx i).val + (2 * s e + 1) < M := by have := (idx (i + 1)).isLt; omega
            have hdest_v : dest.val = (idx i).val + (2 * s e + 1) := by
              simp [dest, Fin.val_add, Nat.mod_eq_of_lt h2se_lt, Nat.mod_eq_of_lt hdv_lt]
            have hlt1 : idx i < idx tdest := by rw [htdest_eq]; change (idx i).val < dest.val; omega
            have hlt2 : idx tdest < idx (i + 1) := by
              rw [htdest_eq]; change dest.val < (idx (i + 1)).val
              by_contra hge
              have heq_v : dest.val = (idx (i + 1)).val := by omega
              exact hne (hidx_mono.injective (Fin.ext (heq_v.symm.trans (congrArg Fin.val htdest_eq).symm)))
            have ht1 : i < tdest := hidx_mono.lt_iff_lt.mp hlt1
            have ht2 : tdest < i + 1 := hidx_mono.lt_iff_lt.mp hlt2
            have hv1 : (i + 1).val = i.val + 1 := by
              rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < mTot), Nat.mod_eq_of_lt hwrap]
            change i.val < tdest.val at ht1; change tdest.val < (i + 1).val at ht2; omega
          · have hi0 : i + 1 = ⟨0, hmTot_pos⟩ := by
              apply Fin.ext; simp only [Fin.val_add, Fin.val_one']
              by_cases hm2 : 1 < mTot
              · rw [Nat.mod_eq_of_lt hm2, show i.val + 1 = mTot by omega, Nat.mod_self]
              · have hm1 : mTot = 1 := by omega
                have hi0' : i.val = 0 := by omega
                simp [hm1, hi0']
            rw [hi0] at hge_next hne
            have hle0 : (idx ⟨0, hmTot_pos⟩).val ≤ (idx i).val := by
              by_cases h0 : (⟨0, hmTot_pos⟩ : Fin mTot) = i
              · rw [h0]
              · exact le_of_lt (hidx_mono (by change 0 < i.val; have := Fin.val_ne_of_ne h0; dsimp at this; omega))
            have hd0 : ((idx ⟨0, hmTot_pos⟩).val + M - (idx i).val) % M =
                (idx ⟨0, hmTot_pos⟩).val + M - (idx i).val := by
              by_cases heq0 : (idx ⟨0, hmTot_pos⟩).val = (idx i).val
              · exfalso; exact hne_i (by rw [hi0]; exact hidx_mono.injective (Fin.ext heq0))
              · exact Nat.mod_eq_of_lt (by omega)
            rw [hd0] at hge_next
            by_cases hwrap2 : (idx i).val + (2 * s e + 1) < M
            · have hdest_v : dest.val = (idx i).val + (2 * s e + 1) := by
                simp [dest, Fin.val_add, Nat.mod_eq_of_lt h2se_lt, Nat.mod_eq_of_lt hwrap2]
              have hlt1 : idx i < idx tdest := by rw [htdest_eq]; change (idx i).val < dest.val; omega
              have ht1 : i < tdest := hidx_mono.lt_iff_lt.mp hlt1
              change i.val < tdest.val at ht1; have := tdest.isLt; omega
            · have hdest_v : dest.val = (idx i).val + (2 * s e + 1) - M := by
                simp only [dest, Fin.val_add, Nat.mod_eq_of_lt h2se_lt]
                rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by have := (idx i).isLt; omega)]
              have hlt0 : idx tdest < idx ⟨0, hmTot_pos⟩ := by
                rw [htdest_eq]; change dest.val < (idx ⟨0, hmTot_pos⟩).val
                by_contra hge
                have heq_v : dest.val = (idx ⟨0, hmTot_pos⟩).val := by omega
                exact hne (hidx_mono.injective (Fin.ext (heq_v.symm.trans (congrArg Fin.val htdest_eq).symm)))
              have ht0 : tdest < ⟨0, hmTot_pos⟩ := hidx_mono.lt_iff_lt.mp hlt0
              change tdest.val < 0 at ht0; omega
        rw [hsucc_eq, htdest_eq]
      have htr := htrav.2.1
      have hdd : ((idx (i + 1)).val + M - (idx i).val) % M = 2 * s e + 1 := by
        have hdist_dest' : (dest.val + M - (idx i).val) % M = 2 * s e + 1 := by
          have hdv : dest.val = ((idx i).val + (2 * s e + 1)) % M := by
            simp [dest, Fin.val_add, Nat.mod_eq_of_lt h2se_lt]
          rw [hdv]
          by_cases hlt : (idx i).val + (2 * s e + 1) < M
          · rw [Nat.mod_eq_of_lt hlt]
            have : (idx i).val + (2 * s e + 1) + M - (idx i).val = (2 * s e + 1) + M := by omega
            rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt h2se_lt]
          · have hlt2 : (idx i).val + (2 * s e + 1) - M < M := by have := (idx i).isLt; omega
            have hgeM : M ≤ (idx i).val + (2 * s e + 1) := by omega
            rw [Nat.mod_eq_sub_mod hgeM, Nat.mod_eq_of_lt hlt2]
            have : (idx i).val + (2 * s e + 1) - M + M - (idx i).val = 2 * s e + 1 := by omega
            rw [this, Nat.mod_eq_of_lt h2se_lt]
        rwa [hdest_eq]
      have htr' : (w (idx i) = Sum.inl (Sum.inl e.1.1) ∧ w (idx (i + 1)) = Sum.inr (Sum.inl e.1.2)) ∨
          (w (idx i) = Sum.inr (Sum.inl e.1.2) ∧ w (idx (i + 1)) = Sum.inl (Sum.inl e.1.1)) := by
        rw [hdest_eq]; exact htr
      exact ⟨e, htr', htrav.2.2, hdd, hdest_eq, h2se_lt⟩
    have hflip : ∀ i : Fin mTot, (w (idx i)).isLeft ≠ (w (idx (i + 1))).isLeft := by
      intro i
      rcases hnext_base i with ⟨e, ⟨h1, h2⟩ | ⟨h1, h2⟩, _, _, _, _⟩ <;> simp [h1, h2]
    have hparity_alt : ∀ i : Fin mTot,
        (w (idx i)).isLeft = xor (w (idx ⟨0, hmTot_pos⟩)).isLeft (i.val % 2 = 1) := by
      intro i
      rcases i with ⟨i, hi⟩
      induction i with
      | zero => simp
      | succ i ih =>
        have h1 := hflip ⟨i, by omega⟩
        have hsucc : (⟨i, by omega⟩ : Fin mTot) + 1 = ⟨i + 1, hi⟩ := by
          apply Fin.ext; simp only [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < mTot), Nat.mod_eq_of_lt hi]
        rw [hsucc] at h1
        have h2 := ih (by omega)
        rw [h2] at h1
        have hm2 : i % 2 = 0 ∨ i % 2 = 1 := by omega
        cases h0 : (w (idx ⟨0, hmTot_pos⟩)).isLeft <;>
        cases hc : (w (idx ⟨i + 1, hi⟩)).isLeft <;>
        rcases hm2 with hm | hm
        all_goals rw [h0, hc] at h1
        all_goals simp only [hm, show (i + 1) % 2 = (i % 2 + 1) % 2 by omega] at h1 ⊢
        all_goals try exact absurd rfl h1
        all_goals try rfl
        all_goals simp at h1 ⊢
    have hm_even : mTot % 2 = 0 := by
      have hlast := hflip ⟨mTot - 1, by omega⟩
      have hsucc : (⟨mTot - 1, by omega⟩ : Fin mTot) + 1 = ⟨0, hmTot_pos⟩ := by
        apply Fin.ext; simp only [Fin.val_add, Fin.val_one']
        by_cases hm2 : 1 < mTot
        · rw [Nat.mod_eq_of_lt hm2, show mTot - 1 + 1 = mTot by omega, Nat.mod_self]
        · have hm1 : mTot = 1 := by omega
          simp [hm1]
      rw [hsucc, hparity_alt ⟨mTot - 1, by omega⟩] at hlast
      have hm2 : mTot % 2 = 0 ∨ mTot % 2 = 1 := by omega
      rcases hm2 with h | h
      · exact h
      · exfalso
        have hodd : (mTot - 1) % 2 = 0 := by omega
        have hv : (⟨mTot - 1, by omega⟩ : Fin mTot).val = mTot - 1 := rfl
        rw [hv, hodd] at hlast
        cases h0 : (w (idx ⟨0, hmTot_pos⟩)).isLeft <;>
          (rw [h0] at hlast; simp only [show ¬ (0 = 1) by decide, decide_false, Bool.xor_false, ne_eq, not_true_eq_false] at hlast)
    have hm_ge2 : 2 ≤ mTot := by omega
    have hgap_val : ∀ i : Fin mTot,
        ((idx (i + 1)).val + M - (idx i).val) % M =
          if i.val + 1 < mTot then (idx (i + 1)).val - (idx i).val
          else (idx ⟨0, hmTot_pos⟩).val + M - (idx i).val := by
      intro i
      split_ifs with hlt
      · have hlt_v : (idx i).val < (idx (i + 1)).val := by
          apply hidx_mono; change i.val < (i + 1).val
          rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < mTot), Nat.mod_eq_of_lt hlt]; omega
        have hsub : (idx (i + 1)).val + M - (idx i).val = ((idx (i + 1)).val - (idx i).val) + M := by omega
        rw [hsub, Nat.add_mod_right, Nat.mod_eq_of_lt (by have := (idx (i + 1)).isLt; omega)]
      · have hi0 : i + 1 = ⟨0, hmTot_pos⟩ := by
          apply Fin.ext; simp only [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < mTot)]
          rw [show i.val + 1 = mTot by omega, Nat.mod_self]
        rw [hi0]
        have hlt_v : (idx ⟨0, hmTot_pos⟩).val < (idx i).val :=
          hidx_mono (by change 0 < i.val; omega)
        exact Nat.mod_eq_of_lt (by have := (idx ⟨0, hmTot_pos⟩).isLt; omega)
    have hsum_gaps : ∑ i : Fin mTot, ((idx (i + 1)).val + M - (idx i).val) % M = M := by
      have htele : ∀ n : ℕ, (hn : n < mTot) →
          ∑ j ∈ Finset.range n,
            (if h : j + 1 < mTot then (idx ⟨j + 1, h⟩).val - (idx ⟨j, by omega⟩).val else 0) =
            (idx ⟨n, hn⟩).val - (idx ⟨0, hmTot_pos⟩).val := by
        intro n
        induction n with
        | zero => intro _; simp
        | succ n ih =>
          intro hn
          rw [Finset.sum_range_succ, ih (by omega)]
          simp only [hn, ↓reduceDIte]
          have hle0 : (idx ⟨0, hmTot_pos⟩).val ≤ (idx ⟨n, by omega⟩).val := by
            by_cases hn0 : n = 0
            · subst hn0; exact le_rfl
            · exact le_of_lt (hidx_mono (by change 0 < n; omega))
          have hle1 : (idx ⟨n, by omega⟩).val ≤ (idx ⟨n + 1, hn⟩).val :=
            le_of_lt (hidx_mono (by change n < n + 1; omega))
          omega
      rw [Finset.sum_fin_eq_sum_range]
      have hrange : Finset.range mTot = Finset.range ((mTot - 1) + 1) := by congr 1; omega
      rw [hrange, Finset.sum_range_succ]
      have hfirst : ∑ j ∈ Finset.range (mTot - 1),
          (if h : j < mTot then ((idx (⟨j, h⟩ + 1)).val + M - (idx ⟨j, h⟩).val) % M else 0) =
          ∑ j ∈ Finset.range (mTot - 1),
            (if h : j + 1 < mTot then (idx ⟨j + 1, h⟩).val - (idx ⟨j, by omega⟩).val else 0) := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        have hjlt : j < mTot - 1 := Finset.mem_range.mp hj
        have hj1 : j + 1 < mTot := by omega
        have hjm : j < mTot := by omega
        simp only [hjm, hj1, ↓reduceDIte]
        rw [hgap_val ⟨j, hjm⟩]
        simp only [hj1, ↓reduceIte]
        have hsucc : (⟨j, hjm⟩ : Fin mTot) + 1 = ⟨j + 1, hj1⟩ := by
          apply Fin.ext; simp only [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < mTot), Nat.mod_eq_of_lt hj1]
        rw [hsucc]
      rw [hfirst, htele (mTot - 1) (by omega)]
      have hlast_lt : mTot - 1 < mTot := by omega
      simp only [hlast_lt, ↓reduceDIte]
      rw [hgap_val ⟨mTot - 1, hlast_lt⟩]
      have hnot : ¬ (mTot - 1 + 1 < mTot) := by omega
      simp only [hnot, ↓reduceIte]
      have hle0 : (idx ⟨0, hmTot_pos⟩).val ≤ (idx ⟨mTot - 1, hlast_lt⟩).val :=
        le_of_lt (hidx_mono (by change 0 < mTot - 1; omega))
      have hltM : (idx ⟨mTot - 1, hlast_lt⟩).val < M := (idx ⟨mTot - 1, hlast_lt⟩).isLt
      omega
    have hm_ge4 : 4 ≤ mTot := by
      by_contra hlt4
      have hm2 : mTot = 2 := by omega
      rcases hnext_base ⟨0, hmTot_pos⟩ with ⟨e0, hdir0, ⟨d0, hd0, hw0⟩, hgap0, hstep0, hlt0⟩
      rcases hnext_base ⟨1, by omega⟩ with ⟨e1, hdir1, ⟨d1, hd1, hw1⟩, hgap1, hstep1, _⟩
      have h01 : (⟨0, hmTot_pos⟩ : Fin mTot) + 1 = ⟨1, by omega⟩ := by
        apply Fin.ext; simp only [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < mTot), zero_add]
      have h10 : (⟨1, by omega⟩ : Fin mTot) + 1 = ⟨0, hmTot_pos⟩ := by
        apply Fin.ext; simp only [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < mTot), show 1 + 1 = mTot by omega, Nat.mod_self]
      rw [h01] at hdir0 hgap0 hstep0
      rw [h10] at hdir1 hgap1 hstep1
      have he01 : e0 = e1 := by
        rcases hdir0 with ⟨h0a, h0b⟩ | ⟨h0a, h0b⟩ <;> rcases hdir1 with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩
        · rw [h0b] at h1a; cases h1a
        · rw [h0a] at h1b; rw [h0b] at h1a
          have hu := Sum.inl.inj (Sum.inl.inj h1b)
          have hv := Sum.inl.inj (Sum.inr.inj h1a)
          exact Subtype.ext (Prod.ext hu hv)
        · rw [h0a] at h1b; rw [h0b] at h1a
          have hu := Sum.inl.inj (Sum.inl.inj h1a)
          have hv := Sum.inl.inj (Sum.inr.inj h1b)
          exact Subtype.ext (Prod.ext hu hv)
        · rw [h0b] at h1a; cases h1a
      subst he01
      have hgv0 := hgap_val ⟨0, hmTot_pos⟩
      have hgv1 := hgap_val ⟨1, by omega⟩
      rw [h01] at hgv0
      rw [h10] at hgv1
      simp only [show 0 + 1 < mTot by omega, ↓reduceIte] at hgv0
      simp only [show ¬ (1 + 1 < mTot) by omega, ↓reduceIte] at hgv1
      have hlt01 : (idx ⟨0, hmTot_pos⟩).val < (idx ⟨1, by omega⟩).val :=
        hidx_mono (by change 0 < 1; omega)
      rw [hgv0] at hgap0
      rw [hgv1] at hgap1
      have hMeq : M = 2 * (2 * s e0 + 1) := by omega
      have heq_idx : idx ⟨0, hmTot_pos⟩ + ⟨(d0 + 1) % M, Nat.mod_lt _ (by omega)⟩ =
          idx ⟨1, by omega⟩ + ⟨(d1 + 1) % M, Nat.mod_lt _ (by omega)⟩ :=
        hw_inj (hw0.trans hw1.symm)
      rw [hstep0, add_assoc] at heq_idx
      have hcancel := add_left_cancel heq_idx
      have hval := congrArg Fin.val hcancel
      simp only [Fin.val_add] at hval
      rw [Nat.mod_eq_of_lt (by omega : d0 + 1 < M),
          Nat.mod_eq_of_lt (by omega : 2 * s e0 + 1 < M),
          Nat.mod_eq_of_lt (by omega : d1 + 1 < M),
          Nat.mod_eq_of_lt (by omega : 2 * s e0 + 1 + (d1 + 1) < M)] at hval
      omega
    let mHalf := mTot / 2
    have hmHalf2 : 2 ≤ mHalf := by omega
    have h2m : 2 * mHalf = mTot := by omega
    let sh : Fin mTot := if (w (idx ⟨0, hmTot_pos⟩)).isLeft then ⟨0, hmTot_pos⟩ else ⟨1, by omega⟩
    let getL : L2 G s earLen ⊕ R2 G s earLen → L := fun z =>
      match z with | Sum.inl (Sum.inl u) => u | _ => uStar
    let getR : L2 G s earLen ⊕ R2 G s earLen → R := fun z =>
      match z with | Sum.inr (Sum.inl v) => v | _ => vStar
    have hsh_L : ∀ i : Fin mHalf, ∃ u : L, w (idx (sh + ⟨2 * i.val, by omega⟩)) = Sum.inl (Sum.inl u) := by
      intro i
      have hval : (sh + ⟨2 * i.val, by omega⟩).val % 2 = if (w (idx ⟨0, hmTot_pos⟩)).isLeft then 0 else 1 := by
        dsimp only [sh]; split_ifs with h0
        · simp only [Fin.val_add, zero_add, Nat.mod_eq_of_lt (by omega : 2 * i.val < mTot)]; omega
        · simp only [Fin.val_add]
          rw [Nat.mod_eq_of_lt (by omega : 1 + 2 * i.val < mTot)]; omega
      have hisL : (w (idx (sh + ⟨2 * i.val, by omega⟩))).isLeft = true := by
        rw [hparity_alt]
        cases h0 : (w (idx ⟨0, hmTot_pos⟩)).isLeft
        · rw [h0] at hval; simp only [Bool.false_eq_true, ↓reduceIte] at hval; rw [hval]; decide
        · rw [h0] at hval; simp only [↓reduceIte] at hval; rw [hval]; decide
      have hbase := hidx_base (sh + ⟨2 * i.val, by omega⟩)
      cases hw : w (idx (sh + ⟨2 * i.val, by omega⟩)) with
      | inl l =>
        cases l with
        | inl u => exact ⟨u, rfl⟩
        | inr _ => rw [hw] at hbase; simp [isBase] at hbase
      | inr _ => rw [hw] at hisL; simp at hisL
    have hsh_R : ∀ i : Fin mHalf, ∃ v : R, w (idx (sh + ⟨2 * i.val + 1, by omega⟩)) = Sum.inr (Sum.inl v) := by
      intro i
      have h1 := hflip (sh + ⟨2 * i.val, by omega⟩)
      have hstep : sh + ⟨2 * i.val, by omega⟩ + 1 = sh + ⟨2 * i.val + 1, by omega⟩ := by
        rw [add_assoc]; congr 1
        apply Fin.ext; simp only [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < mTot), Nat.mod_eq_of_lt (by omega : 2 * i.val + 1 < mTot)]
      rcases hsh_L i with ⟨u, hu⟩
      rw [hstep, hu] at h1
      have hbase := hidx_base (sh + ⟨2 * i.val + 1, by omega⟩)
      cases hw : w (idx (sh + ⟨2 * i.val + 1, by omega⟩)) with
      | inl _ => rw [hw] at h1; simp at h1
      | inr r' =>
        cases r' with
        | inl v => exact ⟨v, rfl⟩
        | inr _ => rw [hw] at hbase; simp [isBase] at hbase
    let u1 : Fin (mHalf - 2 + 2) → L := fun i => getL (w (idx (sh + ⟨2 * i.val, by omega⟩)))
    let v1 : Fin (mHalf - 2 + 2) → R := fun i => getR (w (idx (sh + ⟨2 * i.val + 1, by omega⟩)))
    have hu1_eq : ∀ i : Fin (mHalf - 2 + 2), w (idx (sh + ⟨2 * i.val, by omega⟩)) = Sum.inl (Sum.inl (u1 i)) := by
      intro i; rcases hsh_L ⟨i.val, by omega⟩ with ⟨u, hu⟩; dsimp only [u1, getL]; rw [hu]
    have hv1_eq : ∀ i : Fin (mHalf - 2 + 2), w (idx (sh + ⟨2 * i.val + 1, by omega⟩)) = Sum.inr (Sum.inl (v1 i)) := by
      intro i; rcases hsh_R ⟨i.val, by omega⟩ with ⟨v, hv⟩; dsimp only [v1, getR]; rw [hv]
    have hu1_inj : Function.Injective u1 := by
      intro i j hij
      have h1 : w (idx (sh + ⟨2 * i.val, by omega⟩)) = w (idx (sh + ⟨2 * j.val, by omega⟩)) := by
        rw [hu1_eq i, hu1_eq j, hij]
      have h2 := add_left_cancel (hidx_mono.injective (hw_inj h1))
      have hv := congrArg Fin.val h2; dsimp at hv; exact Fin.ext (by (try dsimp); omega)
    have hv1_inj : Function.Injective v1 := by
      intro i j hij
      have h1 : w (idx (sh + ⟨2 * i.val + 1, by omega⟩)) = w (idx (sh + ⟨2 * j.val + 1, by omega⟩)) := by
        rw [hv1_eq i, hv1_eq j, hij]
      have h2 := add_left_cancel (hidx_mono.injective (hw_inj h1))
      have hv := congrArg Fin.val h2; dsimp at hv; exact Fin.ext (by (try dsimp); omega)
    have hcyc1 : ∀ i : Fin (mHalf - 2 + 2), v1 i ∈ G (u1 i) ∧ v1 i ∈ G (u1 (i + 1)) := by
      intro i
      constructor
      · rcases hnext_base (sh + ⟨2 * i.val, by omega⟩) with ⟨e, hdir, _, _, _, _⟩
        have hstep : (sh + ⟨2 * i.val, by omega⟩) + 1 = sh + ⟨2 * i.val + 1, by omega⟩ := by
          rw [add_assoc]; congr 1
          apply Fin.ext; simp only [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < mTot), Nat.mod_eq_of_lt (by omega : 2 * i.val + 1 < mTot)]
        rw [hstep, hu1_eq i, hv1_eq i] at hdir
        rcases hdir with ⟨hu, hv⟩ | ⟨hbad, _⟩
        · have hu' := Sum.inl.inj (Sum.inl.inj hu)
          have hv' := Sum.inl.inj (Sum.inr.inj hv)
          rw [hu', hv']; exact e.2
        · cases hbad
      · rcases hnext_base (sh + ⟨2 * i.val + 1, by omega⟩) with ⟨e, hdir, _, _, _, _⟩
        have hstep : (sh + ⟨2 * i.val + 1, by omega⟩) + 1 = sh + ⟨2 * (i + 1).val, by have := (i + 1).isLt; omega⟩ := by
          rw [add_assoc]; congr 1
          apply Fin.ext; simp only [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < mTot), Nat.mod_eq_of_lt (by omega : 1 < mHalf - 2 + 2)]
          by_cases hlt : i.val + 1 < mHalf - 2 + 2
          · rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (by omega : 2 * i.val + 1 + 1 < mTot)]; omega
          · have : i.val + 1 = mHalf - 2 + 2 := by omega
            rw [this, Nat.mod_self, mul_zero, show 2 * i.val + 1 + 1 = mTot by omega, Nat.mod_self]
        rw [hstep, hv1_eq i, hu1_eq (i + 1)] at hdir
        rcases hdir with ⟨hbad, _⟩ | ⟨hv, hu⟩
        · cases hbad
        · have hu' := Sum.inl.inj (Sum.inl.inj hu)
          have hv' := Sum.inl.inj (Sum.inr.inj hv)
          rw [hu', hv']; exact e.2
    have hcount : 2 * (mHalf - 2 + 2) * t ≤ a + 2 := by
      have hstep_ge : ∀ i : Fin mTot, 2 * t ≤ ((idx (i + 1)).val + M - (idx i).val) % M := by
        intro i
        rcases hnext_base i with ⟨e, _, _, hgap, _, _⟩
        have := hs e
        omega
      have hsum_le : ∑ _i : Fin mTot, (2 * t) ≤ ∑ i : Fin mTot, ((idx (i + 1)).val + M - (idx i).val) % M :=
        Finset.sum_le_sum (fun i _ => hstep_ge i)
      rw [hsum_gaps] at hsum_le
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hsum_le
      have hmul_eq : mTot * (2 * t) = 2 * (2 * (mHalf - 2 + 2) * t) := by
        have h1 : mTot = 2 * (mHalf - 2 + 2) := by omega
        rw [h1]; ring
      omega
    exact ⟨mHalf - 2, ⟨u1, hu1_inj⟩, ⟨v1, hv1_inj⟩, hcount, hcyc1⟩

noncomputable def sigma2 : GenEdge (G2 G s earLen uStar vStar) → LinEq (GenEdge G) := fun e =>
  match e.1 with
  | (Sum.inl _, Sum.inr (Sum.inl ⟨e0, _⟩)) => ({e0}, false)
  | (Sum.inr (Sum.inl ⟨e0, r⟩), Sum.inr (Sum.inl ⟨_, r'⟩)) =>
      if r.val = r'.val then ({e0}, true) else ({e0}, false)
  | (Sum.inr (Sum.inl ⟨e0, _⟩), Sum.inl _) => ({e0}, false)
  | (Sum.inl _, Sum.inr (Sum.inr _)) => (∅, false)
  | (Sum.inr (Sum.inr r), Sum.inr (Sum.inr r')) =>
      if r.val = r'.val then (∅, true) else (∅, false)
  | (Sum.inr (Sum.inr _), Sum.inl _) => (∅, false)
  | _ => (∅, false)

lemma stretch_sim (hs : ∀ e, 1 ≤ s e) (k : ℕ) (hk : 1 ≤ k)
    (π₂ : List (LinKLine (GenEdge (G2 G s earLen uStar vStar))))
    (hπ₂ : IsLinKRefutation k (genGraphPHP (G2 G s earLen uStar vStar)) π₂) :
    ∃ π₁ : List (LinKLine (GenEdge G)),
      IsLinKRefutation k (genGraphPHP G) π₁ ∧ π₁.length ≤ 1 + 2 * π₂.length := by
  classical
  let A₀ : Clause (GenEdge G) :=
    Finset.univ.filter (fun l : Literal (GenEdge G) => l.1.1.1 = uStar ∧ l.2 = true)
  have hA₀ : A₀ ∈ genGraphPHP G := Or.inl (Or.inl ⟨uStar, rfl⟩)
  have hax : ∀ C ∈ genGraphPHP (G2 G s earLen uStar vStar), ∀ π₀,
      IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' genGraphPHP G) π₀ →
      linKOfClause A₀ ∈ π₀ →
      ∃ π', IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' genGraphPHP G) π' ∧
        (∀ L ∈ π₀, L ∈ π') ∧ substLine (sigma2 G s earLen uStar vStar) (linKOfClause C) ∈ π' ∧
        π'.length ≤ π₀.length + 2 := by
    intro C hC π₀ hder hA0in
    have hM1 : ∀ S ∈ substLine (sigma2 G s earLen uStar vStar) (linKOfClause C), S.card = 1 :=
      substLine_clause_card_one _ C
    have hsat_iff : ∀ a, LinKLineSat a (substLine (sigma2 G s earLen uStar vStar) (linKOfClause C)) ↔
        ∃ l ∈ C, substAssign (sigma2 G s earLen uStar vStar) a l.1 = l.2 := by
      intro a; rw [substLine_sat, linKOfClause_sat_iff]
    have hM_taut : (∀ a : GenEdge G → Bool, LinKLineSat a (substLine (sigma2 G s earLen uStar vStar) (linKOfClause C))) →
        ∃ π', IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' genGraphPHP G) π' ∧
          (∀ L ∈ π₀, L ∈ π') ∧ substLine (sigma2 G s earLen uStar vStar) (linKOfClause C) ∈ π' ∧
          π'.length ≤ π₀.length + 2 := by
      intro htaut
      have hw := isLinKWeakening_one_sem (L := linKOfClause A₀) hM1 (fun a _ => htaut a)
      have hd1 := IsLinKDerivation.weak hder hA0in hw (fun T hT => by rw [hM1 T hT]; exact hk)
      exact ⟨_ :: π₀, hd1, fun L hL => by simp [hL], by simp, by simp⟩
    have hM_from_ax : ∀ (C₀ : Clause (GenEdge G)), C₀ ∈ genGraphPHP G →
        (∀ a : GenEdge G → Bool, (∃ l ∈ C₀, a l.1 = l.2) →
          LinKLineSat a (substLine (sigma2 G s earLen uStar vStar) (linKOfClause C))) →
        ∃ π', IsLinKDerivation k IsLinKWeakening ((fun C => linKOfClause C) '' genGraphPHP G) π' ∧
          (∀ L ∈ π₀, L ∈ π') ∧ substLine (sigma2 G s earLen uStar vStar) (linKOfClause C) ∈ π' ∧
          π'.length ≤ π₀.length + 2 := by
      intro C₀ hC₀ himp
      have hd1 := IsLinKDerivation.ax hder ⟨C₀, hC₀, rfl⟩ (fun T hT => by
        rw [linKOfClause_card_one C₀ T hT]; exact hk)
      have hw : IsLinKWeakening (linKOfClause C₀) (substLine (sigma2 G s earLen uStar vStar) (linKOfClause C)) := by
        apply isLinKWeakening_one_sem hM1
        intro a hsat
        exact himp a ((linKOfClause_sat_iff a C₀).mp hsat)
      have hd2 := IsLinKDerivation.weak hd1 (by simp) hw (fun T hT => by rw [hM1 T hT]; exact hk)
      exact ⟨_ :: linKOfClause C₀ :: π₀, hd2, fun L hL => by simp [hL], by simp, by simp⟩
    rcases hC with (⟨x, rfl⟩ | ⟨e1, e2, he2, hne1, rfl⟩) | ⟨e1, e2, he1, hne2, rfl⟩
    · rcases x with u | ⟨e0, r⟩ | r
      · apply hM_from_ax (Finset.univ.filter (fun l : Literal (GenEdge G) => l.1.1.1 = u ∧ l.2 = true))
          (Or.inl (Or.inl ⟨u, rfl⟩))
        intro a ⟨⟨e0, b⟩, he0, ha⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he0
        rcases he0 with ⟨he0u, rfl⟩
        rw [hsat_iff]
        let e' : GenEdge (G2 G s earLen uStar vStar) :=
          ⟨(Sum.inl u, Sum.inr (Sum.inl ⟨e0, ⟨0, hs e0⟩⟩)),
            (mem_G2_iff G s earLen uStar vStar _ _).mpr ⟨he0u.symm, rfl⟩⟩
        refine ⟨(e', true), by simp [e'], ?_⟩
        simp only [substAssign, sigma2, e', parity_singleton, Bool.xor_false, ha]
      · apply hM_taut; intro a; rw [hsat_iff]
        let eA : GenEdge (G2 G s earLen uStar vStar) :=
          ⟨(Sum.inr (Sum.inl ⟨e0, r⟩), Sum.inr (Sum.inl ⟨e0, r⟩)),
            (mem_G2_iff G s earLen uStar vStar _ _).mpr ⟨rfl, Or.inl rfl⟩⟩
        let eB : GenEdge (G2 G s earLen uStar vStar) :=
          if h : r.val + 1 < s e0 then
            ⟨(Sum.inr (Sum.inl ⟨e0, r⟩), Sum.inr (Sum.inl ⟨e0, ⟨r.val + 1, h⟩⟩)),
              (mem_G2_iff G s earLen uStar vStar _ _).mpr ⟨rfl, Or.inr rfl⟩⟩
          else
            ⟨(Sum.inr (Sum.inl ⟨e0, r⟩), Sum.inl e0.1.2),
              (mem_G2_iff G s earLen uStar vStar _ _).mpr ⟨rfl, by omega⟩⟩
        cases ha : a e0
        · refine ⟨(eA, true), by simp [eA], ?_⟩
          simp only [substAssign, sigma2, eA, ↓reduceIte, parity_singleton, ha]; rfl
        · refine ⟨(eB, true), ?_, ?_⟩
          · dsimp [eB]; split_ifs <;> simp
          · dsimp [eB]; split_ifs with hlt
            · simp only [substAssign, sigma2, show ¬ (r.val = r.val + 1) by omega, ↓reduceIte,
                parity_singleton, Bool.xor_false, ha]
            · simp only [substAssign, sigma2, parity_singleton, Bool.xor_false, ha]
      · apply hM_taut; intro a; rw [hsat_iff]
        let eA : GenEdge (G2 G s earLen uStar vStar) :=
          ⟨(Sum.inr (Sum.inr r), Sum.inr (Sum.inr r)),
            (mem_G2_iff G s earLen uStar vStar _ _).mpr (Or.inl rfl)⟩
        refine ⟨(eA, true), by simp [eA], ?_⟩
        simp only [substAssign, sigma2, eA, ↓reduceIte, parity_empty]; rfl
    · rcases e1 with ⟨⟨x1, y1⟩, h1⟩; rcases e2 with ⟨⟨x2, y2⟩, h2⟩
      dsimp at he2 hne1; subst he2
      rw [mem_G2_iff] at h1 h2
      rcases y1 with v | ⟨e0, r⟩ | r
      · rcases x1 with u1 | ⟨e1', r1⟩ | r1 <;> rcases x2 with u2 | ⟨e2', r2⟩ | r2
        all_goals simp only [adj2Prop] at h1 h2
        all_goals try exact False.elim h1
        all_goals try exact False.elim h2
        · rcases h1 with ⟨hv1, hr1⟩; rcases h2 with ⟨hv2, hr2⟩
          have hne_e : e1'.1.1 ≠ e2'.1.1 := by
            intro hu
            apply hne1
            have heeq : e1' = e2' := Subtype.ext (Prod.ext hu (hv1.symm.trans hv2))
            subst heeq
            congr 2; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext (by (try dsimp); omega)
          apply hM_from_ax {(e1', false), (e2', false)}
            (Or.inl (Or.inr ⟨e1', e2', hv1.symm.trans hv2, hne_e, rfl⟩))
          intro a ⟨l, hl, ha⟩
          rw [hsat_iff]
          simp only [Finset.mem_insert, Finset.mem_singleton] at hl
          rcases hl with rfl | rfl
          · refine ⟨(⟨(Sum.inr (Sum.inl ⟨e1', r1⟩), Sum.inl v), (mem_G2_iff G s earLen uStar vStar _ _).mpr ⟨hv1, hr1⟩⟩, false), by simp, ?_⟩
            simp only [substAssign, sigma2, parity_singleton, Bool.xor_false, ha]
          · refine ⟨(⟨(Sum.inr (Sum.inl ⟨e2', r2⟩), Sum.inl v), (mem_G2_iff G s earLen uStar vStar _ _).mpr ⟨hv2, hr2⟩⟩, false), by simp, ?_⟩
            simp only [substAssign, sigma2, parity_singleton, Bool.xor_false, ha]
        · apply hM_taut; intro a; rw [hsat_iff]
          refine ⟨(⟨(Sum.inr (Sum.inr r2), Sum.inl v), (mem_G2_iff G s earLen uStar vStar _ _).mpr h2⟩, false), by simp, ?_⟩
          simp only [substAssign, sigma2, parity_empty]; rfl
        · apply hM_taut; intro a; rw [hsat_iff]
          refine ⟨(⟨(Sum.inr (Sum.inr r1), Sum.inl v), (mem_G2_iff G s earLen uStar vStar _ _).mpr h1⟩, false), by simp, ?_⟩
          simp only [substAssign, sigma2, parity_empty]; rfl
        · apply hM_taut; intro a; rw [hsat_iff]
          refine ⟨(⟨(Sum.inr (Sum.inr r1), Sum.inl v), (mem_G2_iff G s earLen uStar vStar _ _).mpr h1⟩, false), by simp, ?_⟩
          simp only [substAssign, sigma2, parity_empty]; rfl
      · rcases x1 with u1 | ⟨e1', r1⟩ | r1 <;> rcases x2 with u2 | ⟨e2', r2⟩ | r2
        all_goals simp only [adj2Prop] at h1 h2
        all_goals try exact False.elim h1
        all_goals try exact False.elim h2
        · exfalso; exact hne1 (by rw [h1.1, h2.1])
        · rcases h2 with ⟨rfl, hr2 | hr2⟩
          · apply hM_taut; intro a; rw [hsat_iff]
            cases ha : a e2'
            · refine ⟨(⟨(Sum.inl u1, Sum.inr (Sum.inl ⟨e2', r⟩)), (mem_G2_iff G s earLen uStar vStar _ _).mpr h1⟩, false), by simp, ?_⟩
              simp only [substAssign, sigma2, parity_singleton, Bool.xor_false, ha]
            · refine ⟨(⟨(Sum.inr (Sum.inl ⟨e2', r2⟩), Sum.inr (Sum.inl ⟨e2', r⟩)), (mem_G2_iff G s earLen uStar vStar _ _).mpr ⟨rfl, Or.inl hr2⟩⟩, false), by simp, ?_⟩
              simp only [substAssign, sigma2, hr2, ↓reduceIte, parity_singleton, ha]; rfl
          · omega
        · rcases h1 with ⟨rfl, hr1 | hr1⟩
          · apply hM_taut; intro a; rw [hsat_iff]
            cases ha : a e1'
            · refine ⟨(⟨(Sum.inl u2, Sum.inr (Sum.inl ⟨e1', r⟩)), (mem_G2_iff G s earLen uStar vStar _ _).mpr h2⟩, false), by simp, ?_⟩
              simp only [substAssign, sigma2, parity_singleton, Bool.xor_false, ha]
            · refine ⟨(⟨(Sum.inr (Sum.inl ⟨e1', r1⟩), Sum.inr (Sum.inl ⟨e1', r⟩)), (mem_G2_iff G s earLen uStar vStar _ _).mpr ⟨rfl, Or.inl hr1⟩⟩, false), by simp, ?_⟩
              simp only [substAssign, sigma2, hr1, ↓reduceIte, parity_singleton, ha]; rfl
          · omega
        · rcases h1 with ⟨rfl, hr1 | hr1⟩ <;> rcases h2 with ⟨rfl, hr2 | hr2⟩
          · exfalso; apply hne1; congr 2; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext (hr1.trans hr2.symm)
          · apply hM_taut; intro a; rw [hsat_iff]
            cases ha : a e2'
            · refine ⟨(⟨(Sum.inr (Sum.inl ⟨e2', r2⟩), Sum.inr (Sum.inl ⟨e2', r⟩)), (mem_G2_iff G s earLen uStar vStar _ _).mpr ⟨rfl, Or.inr hr2⟩⟩, false), by simp, ?_⟩
              simp only [substAssign, sigma2, show ¬ (r2.val = r.val) by omega, ↓reduceIte, parity_singleton, Bool.xor_false, ha]
            · refine ⟨(⟨(Sum.inr (Sum.inl ⟨e2', r1⟩), Sum.inr (Sum.inl ⟨e2', r⟩)), (mem_G2_iff G s earLen uStar vStar _ _).mpr ⟨rfl, Or.inl hr1⟩⟩, false), by simp, ?_⟩
              simp only [substAssign, sigma2, hr1, ↓reduceIte, parity_singleton, ha]; rfl
          · apply hM_taut; intro a; rw [hsat_iff]
            cases ha : a e2'
            · refine ⟨(⟨(Sum.inr (Sum.inl ⟨e2', r1⟩), Sum.inr (Sum.inl ⟨e2', r⟩)), (mem_G2_iff G s earLen uStar vStar _ _).mpr ⟨rfl, Or.inr hr1⟩⟩, false), by simp, ?_⟩
              simp only [substAssign, sigma2, show ¬ (r1.val = r.val) by omega, ↓reduceIte, parity_singleton, Bool.xor_false, ha]
            · refine ⟨(⟨(Sum.inr (Sum.inl ⟨e2', r2⟩), Sum.inr (Sum.inl ⟨e2', r⟩)), (mem_G2_iff G s earLen uStar vStar _ _).mpr ⟨rfl, Or.inl hr2⟩⟩, false), by simp, ?_⟩
              simp only [substAssign, sigma2, hr2, ↓reduceIte, parity_singleton, ha]; rfl
          · exfalso; apply hne1; congr 2; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext (by dsimp; omega)
      · rcases x1 with u1 | ⟨e1', r1⟩ | r1 <;> rcases x2 with u2 | ⟨e2', r2⟩ | r2
        all_goals simp only [adj2Prop] at h1 h2
        all_goals try exact False.elim h1
        all_goals try exact False.elim h2
        · exfalso; exact hne1 (by rw [h1.1, h2.1])
        · apply hM_taut; intro a; rw [hsat_iff]
          refine ⟨(⟨(Sum.inl u1, Sum.inr (Sum.inr r)), (mem_G2_iff G s earLen uStar vStar _ _).mpr h1⟩, false), by simp, ?_⟩
          simp only [substAssign, sigma2, parity_empty]; rfl
        · apply hM_taut; intro a; rw [hsat_iff]
          refine ⟨(⟨(Sum.inl u2, Sum.inr (Sum.inr r)), (mem_G2_iff G s earLen uStar vStar _ _).mpr h2⟩, false), by simp, ?_⟩
          simp only [substAssign, sigma2, parity_empty]; rfl
        · rcases h1 with hr1 | hr1 <;> rcases h2 with hr2 | hr2
          · exfalso; apply hne1; congr 2; exact Fin.ext (hr1.trans hr2.symm)
          · apply hM_taut; intro a; rw [hsat_iff]
            refine ⟨(⟨(Sum.inr (Sum.inr r2), Sum.inr (Sum.inr r)), (mem_G2_iff G s earLen uStar vStar _ _).mpr (Or.inr hr2)⟩, false), by simp, ?_⟩
            simp only [substAssign, sigma2, show ¬ (r2.val = r.val) by omega, ↓reduceIte, parity_empty]; rfl
          · apply hM_taut; intro a; rw [hsat_iff]
            refine ⟨(⟨(Sum.inr (Sum.inr r1), Sum.inr (Sum.inr r)), (mem_G2_iff G s earLen uStar vStar _ _).mpr (Or.inr hr1)⟩, false), by simp, ?_⟩
            simp only [substAssign, sigma2, show ¬ (r1.val = r.val) by omega, ↓reduceIte, parity_empty]; rfl
          · exfalso; apply hne1; congr 2; exact Fin.ext (by (try dsimp); omega)
    · rcases e1 with ⟨⟨x1, y1⟩, h1⟩; rcases e2 with ⟨⟨x2, y2⟩, h2⟩
      dsimp at he1 hne2; subst he1
      rw [mem_G2_iff] at h1 h2
      rcases x1 with u | ⟨e0, r⟩ | r
      · rcases y1 with v1 | ⟨e1', r1⟩ | r1 <;> rcases y2 with v2 | ⟨e2', r2⟩ | r2
        all_goals simp only [adj2Prop] at h1 h2
        all_goals try exact False.elim h1
        all_goals try exact False.elim h2
        · rcases h1 with ⟨hu1, hr1⟩; rcases h2 with ⟨hu2, hr2⟩
          have hne_v : e1'.1.2 ≠ e2'.1.2 := by
            intro hv
            apply hne2
            have heeq : e1' = e2' := Subtype.ext (Prod.ext (hu1.symm.trans hu2) hv)
            subst heeq
            congr 2; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext (hr1.trans hr2.symm)
          apply hM_from_ax {(e1', false), (e2', false)}
            (Or.inr ⟨e1', e2', hu1.symm.trans hu2, hne_v, rfl⟩)
          intro a ⟨l, hl, ha⟩
          rw [hsat_iff]
          simp only [Finset.mem_insert, Finset.mem_singleton] at hl
          rcases hl with rfl | rfl
          · refine ⟨(⟨(Sum.inl u, Sum.inr (Sum.inl ⟨e1', r1⟩)), (mem_G2_iff G s earLen uStar vStar _ _).mpr ⟨hu1, hr1⟩⟩, false), by simp, ?_⟩
            simp only [substAssign, sigma2, parity_singleton, Bool.xor_false, ha]
          · refine ⟨(⟨(Sum.inl u, Sum.inr (Sum.inl ⟨e2', r2⟩)), (mem_G2_iff G s earLen uStar vStar _ _).mpr ⟨hu2, hr2⟩⟩, false), by simp, ?_⟩
            simp only [substAssign, sigma2, parity_singleton, Bool.xor_false, ha]
        · apply hM_taut; intro a; rw [hsat_iff]
          refine ⟨(⟨(Sum.inl u, Sum.inr (Sum.inr r2)), (mem_G2_iff G s earLen uStar vStar _ _).mpr h2⟩, false), by simp, ?_⟩
          simp only [substAssign, sigma2, parity_empty]; rfl
        · apply hM_taut; intro a; rw [hsat_iff]
          refine ⟨(⟨(Sum.inl u, Sum.inr (Sum.inr r1)), (mem_G2_iff G s earLen uStar vStar _ _).mpr h1⟩, false), by simp, ?_⟩
          simp only [substAssign, sigma2, parity_empty]; rfl
        · apply hM_taut; intro a; rw [hsat_iff]
          refine ⟨(⟨(Sum.inl u, Sum.inr (Sum.inr r1)), (mem_G2_iff G s earLen uStar vStar _ _).mpr h1⟩, false), by simp, ?_⟩
          simp only [substAssign, sigma2, parity_empty]; rfl
      · rcases y1 with v1 | ⟨e1', r1⟩ | r1 <;> rcases y2 with v2 | ⟨e2', r2⟩ | r2
        all_goals simp only [adj2Prop] at h1 h2
        all_goals try exact False.elim h1
        all_goals try exact False.elim h2
        · exfalso; exact hne2 (by rw [h1.1, h2.1])
        · rcases h2 with ⟨rfl, hr2 | hr2⟩
          · apply hM_taut; intro a; rw [hsat_iff]
            cases ha : a e0
            · refine ⟨(⟨(Sum.inr (Sum.inl ⟨e0, r⟩), Sum.inl v1), (mem_G2_iff G s earLen uStar vStar _ _).mpr h1⟩, false), by simp, ?_⟩
              simp only [substAssign, sigma2, parity_singleton, Bool.xor_false, ha]
            · refine ⟨(⟨(Sum.inr (Sum.inl ⟨e0, r⟩), Sum.inr (Sum.inl ⟨e0, r2⟩)), (mem_G2_iff G s earLen uStar vStar _ _).mpr ⟨rfl, Or.inl hr2⟩⟩, false), by simp, ?_⟩
              simp only [substAssign, sigma2, hr2, ↓reduceIte, parity_singleton, ha]; rfl
          · have := r2.isLt; omega
        · rcases h1 with ⟨rfl, hr1 | hr1⟩
          · apply hM_taut; intro a; rw [hsat_iff]
            cases ha : a e0
            · refine ⟨(⟨(Sum.inr (Sum.inl ⟨e0, r⟩), Sum.inl v2), (mem_G2_iff G s earLen uStar vStar _ _).mpr h2⟩, false), by simp, ?_⟩
              simp only [substAssign, sigma2, parity_singleton, Bool.xor_false, ha]
            · refine ⟨(⟨(Sum.inr (Sum.inl ⟨e0, r⟩), Sum.inr (Sum.inl ⟨e0, r1⟩)), (mem_G2_iff G s earLen uStar vStar _ _).mpr ⟨rfl, Or.inl hr1⟩⟩, false), by simp, ?_⟩
              simp only [substAssign, sigma2, hr1, ↓reduceIte, parity_singleton, ha]; rfl
          · have := r1.isLt; omega
        · rcases h1 with ⟨rfl, hr1 | hr1⟩ <;> rcases h2 with ⟨rfl, hr2 | hr2⟩
          · exfalso; apply hne2; congr 2; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext (hr1.symm.trans hr2)
          · apply hM_taut; intro a; rw [hsat_iff]
            cases ha : a e0
            · refine ⟨(⟨(Sum.inr (Sum.inl ⟨e0, r⟩), Sum.inr (Sum.inl ⟨e0, r2⟩)), (mem_G2_iff G s earLen uStar vStar _ _).mpr ⟨rfl, Or.inr hr2⟩⟩, false), by simp, ?_⟩
              simp only [substAssign, sigma2, show ¬ (r.val = r2.val) by omega, ↓reduceIte, parity_singleton, Bool.xor_false, ha]
            · refine ⟨(⟨(Sum.inr (Sum.inl ⟨e0, r⟩), Sum.inr (Sum.inl ⟨e0, r1⟩)), (mem_G2_iff G s earLen uStar vStar _ _).mpr ⟨rfl, Or.inl hr1⟩⟩, false), by simp, ?_⟩
              simp only [substAssign, sigma2, hr1, ↓reduceIte, parity_singleton, ha]; rfl
          · apply hM_taut; intro a; rw [hsat_iff]
            cases ha : a e0
            · refine ⟨(⟨(Sum.inr (Sum.inl ⟨e0, r⟩), Sum.inr (Sum.inl ⟨e0, r1⟩)), (mem_G2_iff G s earLen uStar vStar _ _).mpr ⟨rfl, Or.inr hr1⟩⟩, false), by simp, ?_⟩
              simp only [substAssign, sigma2, show ¬ (r.val = r1.val) by omega, ↓reduceIte, parity_singleton, Bool.xor_false, ha]
            · refine ⟨(⟨(Sum.inr (Sum.inl ⟨e0, r⟩), Sum.inr (Sum.inl ⟨e0, r2⟩)), (mem_G2_iff G s earLen uStar vStar _ _).mpr ⟨rfl, Or.inl hr2⟩⟩, false), by simp, ?_⟩
              simp only [substAssign, sigma2, hr2, ↓reduceIte, parity_singleton, ha]; rfl
          · exfalso; apply hne2; congr 2; refine Sigma.ext rfl (heq_of_eq ?_); exact Fin.ext (by dsimp; omega)
      · rcases y1 with v1 | ⟨e1', r1⟩ | r1 <;> rcases y2 with v2 | ⟨e2', r2⟩ | r2
        all_goals simp only [adj2Prop] at h1 h2
        all_goals try exact False.elim h1
        all_goals try exact False.elim h2
        · exfalso; exact hne2 (by rw [h1.1, h2.1])
        · apply hM_taut; intro a; rw [hsat_iff]
          refine ⟨(⟨(Sum.inr (Sum.inr r), Sum.inl v1), (mem_G2_iff G s earLen uStar vStar _ _).mpr h1⟩, false), by simp, ?_⟩
          simp only [substAssign, sigma2, parity_empty]; rfl
        · apply hM_taut; intro a; rw [hsat_iff]
          refine ⟨(⟨(Sum.inr (Sum.inr r), Sum.inl v2), (mem_G2_iff G s earLen uStar vStar _ _).mpr h2⟩, false), by simp, ?_⟩
          simp only [substAssign, sigma2, parity_empty]; rfl
        · rcases h1 with hr1 | hr1 <;> rcases h2 with hr2 | hr2
          · exfalso; apply hne2; congr 2; exact Fin.ext (hr1.symm.trans hr2)
          · apply hM_taut; intro a; rw [hsat_iff]
            refine ⟨(⟨(Sum.inr (Sum.inr r), Sum.inr (Sum.inr r2)), (mem_G2_iff G s earLen uStar vStar _ _).mpr (Or.inr hr2)⟩, false), by simp, ?_⟩
            simp only [substAssign, sigma2, show ¬ (r.val = r2.val) by omega, ↓reduceIte, parity_empty]; rfl
          · apply hM_taut; intro a; rw [hsat_iff]
            refine ⟨(⟨(Sum.inr (Sum.inr r), Sum.inr (Sum.inr r1)), (mem_G2_iff G s earLen uStar vStar _ _).mpr (Or.inr hr1)⟩, false), by simp, ?_⟩
            simp only [substAssign, sigma2, show ¬ (r.val = r1.val) by omega, ↓reduceIte, parity_empty]; rfl
          · exfalso; apply hne2; congr 2; exact Fin.ext (by (try dsimp); omega)
  have hsim := affine_sim k 2 hk (genGraphPHP G) (genGraphPHP (G2 G s earLen uStar vStar)) A₀ hA₀
    (sigma2 G s earLen uStar vStar) hax π₂ hπ₂
  simpa using hsim

end StretchAndEar

section MainAssembly

lemma pow2_ge_sq (m : ℕ) (hm : 30 ≤ m) : 1280 * m ^ 2 ≤ 2 ^ (m - 1) := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have h1 : 1280 * (m + 1) ^ 2 ≤ 2 * (1280 * m ^ 2) := by nlinarith
    have h2 : 2 ^ (m + 1 - 1) = 2 * 2 ^ (m - 1) := by
      have : m + 1 - 1 = (m - 1) + 1 := by omega
      rw [this, pow_succ]; ring
    rw [h2]
    omega

lemma clog_sq_bound (N : ℕ) (hN : 2 ^ 30 ≤ N) :
    1280 * (Nat.clog 2 N) ^ 2 ≤ N := by
  have hN1 : 1 < N := by
    have : 2 ≤ 2 ^ 30 := by decide
    omega
  have hc1 : 30 ≤ Nat.clog 2 N := by
    have hle : 2 ^ 30 ≤ 2 ^ Nat.clog 2 N := le_trans hN (Nat.le_pow_clog (by omega) N)
    exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hle
  have hlt : 2 ^ (Nat.clog 2 N - 1) < N := by
    simpa [Nat.pred_eq_sub_one] using Nat.pow_pred_clog_lt_self 2 hN1
  have hsq := pow2_ge_sq (Nat.clog 2 N) hc1
  omega

lemma real_exp_ge_pow_two_mul (ell d : ℕ) (hell : 30 ≤ ell) (hd : 1 ≤ d) (N : ℕ) (hN : N ≤ 2 ^ ell) :
    (4800 * (N : ℝ) ^ d + 4800) < Real.exp (64 * (d : ℝ) * (ell : ℝ)) := by
  have hN_le : (N : ℝ) ≤ Real.exp (ell : ℝ) := by
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have h1 : (N : ℝ) ≤ (2 : ℝ) ^ ell := by exact_mod_cast hN
    calc (N : ℝ) ≤ (2 : ℝ) ^ ell := h1
      _ ≤ (Real.exp 1) ^ ell := pow_le_pow_left₀ (by norm_num) h2e ell
      _ = Real.exp (ell : ℝ) := by rw [← Real.exp_nat_mul]; simp
  have hNd : (N : ℝ) ^ d ≤ Real.exp ((d : ℝ) * (ell : ℝ)) := by
    calc (N : ℝ) ^ d ≤ (Real.exp (ell : ℝ)) ^ d := pow_le_pow_left₀ (Nat.cast_nonneg N) hN_le d
      _ = Real.exp ((d : ℝ) * (ell : ℝ)) := by rw [← Real.exp_nat_mul]
  have hexp1 : (1 : ℝ) ≤ Real.exp ((d : ℝ) * (ell : ℝ)) :=
    Real.one_le_exp (by positivity)
  have h4800 : (9600 : ℝ) < Real.exp (10 : ℝ) := by
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have h10 : (1024 : ℝ) ≤ Real.exp 10 := by
      calc (1024 : ℝ) = (2 : ℝ) ^ 10 := by norm_num
        _ ≤ (Real.exp 1) ^ 10 := pow_le_pow_left₀ (by norm_num) h2e 10
        _ = Real.exp 10 := by rw [← Real.exp_nat_mul]; norm_num
    have h3 : (2.7 : ℝ) ≤ Real.exp 1 := by
      have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1) 5
      simp [Finset.sum_range_succ, Nat.factorial] at h
      linarith
    have h10' : (2.7 : ℝ) ^ 10 ≤ Real.exp 10 := by
      calc (2.7 : ℝ) ^ 10 ≤ (Real.exp 1) ^ 10 := pow_le_pow_left₀ (by norm_num) h3 10
        _ = Real.exp 10 := by rw [← Real.exp_nat_mul]; norm_num
    have hnum : (9600 : ℝ) < (2.7 : ℝ) ^ 10 := by norm_num
    linarith
  have hdell : (10 : ℝ) + (d : ℝ) * (ell : ℝ) ≤ 64 * (d : ℝ) * (ell : ℝ) := by
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
    have he30 : (30 : ℝ) ≤ ell := by exact_mod_cast hell
    nlinarith
  calc (4800 * (N : ℝ) ^ d + 4800)
      ≤ 4800 * Real.exp ((d : ℝ) * (ell : ℝ)) + 4800 * Real.exp ((d : ℝ) * (ell : ℝ)) := by nlinarith
    _ = 9600 * Real.exp ((d : ℝ) * (ell : ℝ)) := by ring
    _ < Real.exp 10 * Real.exp ((d : ℝ) * (ell : ℝ)) :=
        mul_lt_mul_of_pos_right h4800 (Real.exp_pos _)
    _ = Real.exp (10 + (d : ℝ) * (ell : ℝ)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (64 * (d : ℝ) * (ell : ℝ)) := Real.exp_le_exp.mpr hdell

lemma final_bound_355 (C₀ C q₀ k d ell N h len₀ len : ℕ)
    (hC₀2 : 2 ≤ C₀) (hC2 : 2 ≤ C) (hC_ge_B : 268435456 * C₀ ^ 3 ≤ C)
    (hCh : C ≤ h) (hell30 : 30 ≤ ell) (hN_le_pow : N ≤ 2 ^ ell)
    (hQ_le_Cq : h * ell ≤ C₀ * q₀) (hk : 1 ≤ k) (hd : 1 ≤ d) (hCkd : C ^ k * d ≤ h)
    (hlen_tot : len₀ ≤ 4800 * len + 4800)
    (hgb_fn : 2 * (C₀ * 16) * (16 * k + 4 * 16) ≤ q₀ → 4 * (C₀ * 16) + C₀ ≤ q₀ →
      Real.exp ((1 / (16 * (C₀ : ℝ) * (16 : ℝ) ^ 2)) ^ k / (32 * (k : ℝ) * (C₀ : ℝ) * 16) * (q₀ : ℝ)) ≤ (len₀ : ℝ)) :
    N ^ d < len := by
  have hk_le_2pow : k ≤ 2 ^ k := Nat.lt_two_pow_self.le
  have hCk_ge_Ck : C * k ≤ C ^ k := by
    have hkm1 : k ≤ 2 ^ (k - 1) := by
      have hk1 : ∀ m : ℕ, m + 1 ≤ 2 ^ m := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
          rw [pow_succ]; have : 1 ≤ 2 ^ m := Nat.one_le_two_pow; omega
      have := hk1 (k - 1)
      have hsub : k - 1 + 1 = k := by omega
      rwa [hsub] at this
    calc C * k ≤ C * 2 ^ (k - 1) := Nat.mul_le_mul_left C hkm1
      _ ≤ C * C ^ (k - 1) := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hC2 (k - 1))
      _ = C ^ (k - 1 + 1) := by rw [pow_succ, mul_comm]
      _ = C ^ k := by rw [show k - 1 + 1 = k by omega]
  have hn1 : 2 * (C₀ * 16) * (16 * k + 4 * 16) ≤ q₀ := by
    have hmul : C₀ * (2 * (C₀ * 16) * (16 * k + 4 * 16)) ≤ C₀ * q₀ := by
      have h1 : 2 * (C₀ * 16) * (16 * k + 4 * 16) * C₀ ≤ (2560 * C₀ ^ 2) * k := by
        have : 16 * k + 4 * 16 ≤ 80 * k := by omega
        calc 2 * (C₀ * 16) * (16 * k + 4 * 16) * C₀
            = 32 * C₀ ^ 2 * (16 * k + 4 * 16) := by ring
          _ ≤ 32 * C₀ ^ 2 * (80 * k) := Nat.mul_le_mul_left _ this
          _ = (2560 * C₀ ^ 2) * k := by ring
      have h2 : 2560 * C₀ ^ 2 ≤ C := by
        have : C₀ ^ 2 ≤ C₀ ^ 3 := Nat.pow_le_pow_right (by omega : 0 < C₀) (by decide : 2 ≤ 3)
        omega
      have h3 : (2560 * C₀ ^ 2) * k ≤ h * ell := by
        calc (2560 * C₀ ^ 2) * k ≤ C * k := Nat.mul_le_mul_right k h2
          _ ≤ C ^ k := hCk_ge_Ck
          _ = C ^ k * 1 := (mul_one _).symm
          _ ≤ C ^ k * d := Nat.mul_le_mul_left _ hd
          _ ≤ h := hCkd
          _ = h * 1 := (mul_one h).symm
          _ ≤ h * ell := Nat.mul_le_mul_left h (by omega)
      have hcomm : C₀ * (2 * (C₀ * 16) * (16 * k + 4 * 16)) = 2 * (C₀ * 16) * (16 * k + 4 * 16) * C₀ := by ring
      rw [hcomm]
      exact le_trans h1 (le_trans h3 hQ_le_Cq)
    exact Nat.le_of_mul_le_mul_left hmul (by omega)
  have hn2 : 4 * (C₀ * 16) + C₀ ≤ q₀ := by
    have hmul : C₀ * (4 * (C₀ * 16) + C₀) ≤ C₀ * q₀ := by
      have h1 : C₀ * (4 * (C₀ * 16) + C₀) = 65 * C₀ ^ 2 := by ring
      rw [h1]
      have h2 : 65 * C₀ ^ 2 ≤ C := by
        have : C₀ ^ 2 ≤ C₀ ^ 3 := Nat.pow_le_pow_right (by omega : 0 < C₀) (by decide : 2 ≤ 3)
        omega
      have h3 : C ≤ h * ell := by
        calc C ≤ h := hCh
          _ = h * 1 := (mul_one h).symm
          _ ≤ h * ell := Nat.mul_le_mul_left h (by omega)
      exact le_trans h2 (le_trans h3 hQ_le_Cq)
    exact Nat.le_of_mul_le_mul_left hmul (by omega)
  have hgb := hgb_fn hn1 hn2
  have hexp_nat : 64 * d * ell * (32 * k * C₀ * 16) * (16 * C₀ * 16 ^ 2) ^ k ≤ q₀ := by
    have hmul : C₀ * (64 * d * ell * (32 * k * C₀ * 16) * (16 * C₀ * 16 ^ 2) ^ k) ≤ C₀ * q₀ := by
      have hA : 32768 * C₀ ^ 2 ≤ (32768 * C₀ ^ 2) ^ k :=
        Nat.le_self_pow (by omega : k ≠ 0) (32768 * C₀ ^ 2)
      have hB : 32768 * C₀ ^ 2 * k * (4096 * C₀) ^ k ≤ C ^ k := by
        calc 32768 * C₀ ^ 2 * k * (4096 * C₀) ^ k
            ≤ (32768 * C₀ ^ 2) ^ k * 2 ^ k * (4096 * C₀) ^ k := by
              have h1 := Nat.mul_le_mul hA hk_le_2pow
              exact Nat.mul_le_mul_right _ h1
          _ = (268435456 * C₀ ^ 3) ^ k := by rw [← mul_pow, ← mul_pow]; congr 1; ring
          _ ≤ C ^ k := Nat.pow_le_pow_left hC_ge_B k
      have heq : C₀ * (64 * d * ell * (32 * k * C₀ * 16) * (16 * C₀ * 16 ^ 2) ^ k) =
          (32768 * C₀ ^ 2 * k * (4096 * C₀) ^ k) * d * ell := by ring
      rw [heq]
      calc (32768 * C₀ ^ 2 * k * (4096 * C₀) ^ k) * d * ell
          ≤ C ^ k * d * ell := Nat.mul_le_mul_right ell (Nat.mul_le_mul_right d hB)
        _ ≤ h * ell := Nat.mul_le_mul_right ell hCkd
        _ ≤ C₀ * q₀ := hQ_le_Cq
    exact Nat.le_of_mul_le_mul_left hmul (by omega)
  have hexp_real : 64 * (d : ℝ) * (ell : ℝ) ≤
      (1 / (16 * (C₀ : ℝ) * (16 : ℝ) ^ 2)) ^ k / (32 * (k : ℝ) * (C₀ : ℝ) * 16) * (q₀ : ℝ) := by
    have hC0R : (0 : ℝ) < (C₀ : ℝ) := by exact_mod_cast (by omega : 0 < C₀)
    have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hden1 : (0 : ℝ) < (16 * (C₀ : ℝ) * (16 : ℝ) ^ 2) ^ k := by positivity
    have hden2 : (0 : ℝ) < 32 * (k : ℝ) * (C₀ : ℝ) * 16 := by positivity
    have hnatR : (64 * (d : ℝ) * (ell : ℝ)) * (32 * (k : ℝ) * (C₀ : ℝ) * 16) *
        (16 * (C₀ : ℝ) * (16 : ℝ) ^ 2) ^ k ≤ (q₀ : ℝ) := by
      exact_mod_cast hexp_nat
    have hrew : (1 / (16 * (C₀ : ℝ) * (16 : ℝ) ^ 2)) ^ k / (32 * (k : ℝ) * (C₀ : ℝ) * 16) * (q₀ : ℝ) =
        (q₀ : ℝ) / ((32 * (k : ℝ) * (C₀ : ℝ) * 16) * (16 * (C₀ : ℝ) * (16 : ℝ) ^ 2) ^ k) := by
      rw [one_div, inv_pow]
      field_simp
    rw [hrew, le_div_iff₀ (mul_pos hden2 hden1)]
    linarith
  have h1 := real_exp_ge_pow_two_mul ell d hell30 hd N hN_le_pow
  have h2 : Real.exp (64 * (d : ℝ) * (ell : ℝ)) ≤ (len₀ : ℝ) :=
    le_trans (Real.exp_le_exp.mpr hexp_real) hgb
  have h3 : (len₀ : ℝ) ≤ 4800 * (len : ℝ) + 4800 := by exact_mod_cast hlen_tot
  have hltR : (N : ℝ) ^ d < (len : ℝ) := by linarith
  exact_mod_cast hltR

lemma card_eq_of_fintype {α : Type} (i1 i2 : Fintype α) :
    @Fintype.card α i1 = @Fintype.card α i2 :=
  @Fintype.card_congr α α i1 i2 (Equiv.refl α)

lemma isLinKRefutation_genGraphPHP_cast {L R : Type}
    (fL1 fL2 : Fintype L) (fR1 fR2 : Fintype R)
    (dL1 dL2 : DecidableEq L) (dR1 dR2 : DecidableEq R)
    (G : GenBip L R)
    (d1 d2 : DecidableEq (GenEdge G)) (k : ℕ) (π : List (LinKLine (GenEdge G)))
    (h : @IsLinKRefutation (GenEdge G) d1 k (@genGraphPHP L R fL1 fR1 dL1 dR1 G) π) :
    @IsLinKRefutation (GenEdge G) d2 k (@genGraphPHP L R fL2 fR2 dL2 dR2 G) π := by
  have h1 : fL1 = fL2 := Subsingleton.elim _ _
  have h2 : fR1 = fR2 := Subsingleton.elim _ _
  have h3 : dL1 = dL2 := Subsingleton.elim _ _
  have h4 : dR1 = dR2 := Subsingleton.elim _ _
  have h5 : d1 = d2 := Subsingleton.elim _ _
  subst h1; subst h2; subst h3; subst h4; subst h5
  exact h

end MainAssembly

end PEqualNP.Outside.L_pcx_355_aux

set_option maxHeartbeats 1600000 in
theorem PEqualNP.Outside.L_pcx_355 : (∃ C N₀ : ℕ, 2 ≤ C ∧ ∀ N : ℕ, N₀ ≤ N →
  let ell := Nat.clog 2 N
  ∀ h : ℕ, C ≤ h → h ≤ ell →
    ∃ q : ℕ, ∃ G : PEqualNP.Expanders.BipGraph (q+1) q,
      Fintype.card (PEqualNP.Expanders.GEdge G) = N ∧
      (∀ u, 2 ≤ (G u).card ∧ (G u).card ≤ 3) ∧
      (∀ v, 2 ≤ (PEqualNP.Expanders.rightNbrs G v).card ∧
        (PEqualNP.Expanders.rightNbrs G v).card ≤ 3) ∧
      (∀ f : Fin (q+1) ⊕ Fin q → Bool,
        (∀ u, ∀ v ∈ G u, f (Sum.inl u) = f (Sum.inr v)) → ∀ x y, f x = f y) ∧
      (∀ (a : ℕ) (us : Fin (a+2) ↪ Fin (q+1)) (vs : Fin (a+2) ↪ Fin q),
        (∀ i, vs i ∈ G (us i) ∧ vs i ∈ G (us (i+1))) →
        N*Nat.clog 2 (ell+1) ≤ C*(2*(a+2))*h*ell) ∧
      ∀ k d : ℕ, 1 ≤ k → 1 ≤ d → C^k*d ≤ h →
        let refutes := PEqualNP.ProofComplexity.IsLinKRefutation k
          (PEqualNP.Expanders.funGraphPHP G)
        (∃ π : List (PEqualNP.ProofComplexity.LinKLine (PEqualNP.Expanders.GEdge G)),
          refutes π) ∧
        ∀ π : List (PEqualNP.ProofComplexity.LinKLine (PEqualNP.Expanders.GEdge G)),
          refutes π → N^d < π.length) := by
  classical
  obtain ⟨C₀, Q₀, hC₀2, h352⟩ := PEqualNP.Outside.L_pcx_352
  let C : ℕ := max Q₀ (268435456 * C₀ ^ 3)
  have hC_ge_Q0 : Q₀ ≤ C := le_max_left _ _
  have hC_ge_B : 268435456 * C₀ ^ 3 ≤ C := le_max_right _ _
  have hC₀3 : 8 ≤ C₀ ^ 3 := by
    have : 2 ^ 3 ≤ C₀ ^ 3 := Nat.pow_le_pow_left hC₀2 3
    omega
  have hC2 : 2 ≤ C := by omega
  refine ⟨C, 2 ^ 30, hC2, ?_⟩
  intro N hN
  dsimp only
  set ell := Nat.clog 2 N with hell_def
  intro h hCh hhell
  have hell30 : 30 ≤ ell := by
    have hle : 2 ^ 30 ≤ 2 ^ ell := le_trans hN (Nat.le_pow_clog (by omega) N)
    exact (Nat.pow_le_pow_iff_right (by omega : 1 < 2)).mp hle
  have hN_le_pow : N ≤ 2 ^ ell := Nat.le_pow_clog (by omega) N
  have hclog_sq : 1280 * ell ^ 2 ≤ N := PEqualNP.Outside.L_pcx_355_aux.clog_sq_bound N hN
  let Q : ℕ := h * ell
  have hQ_ge_Q0 : Q₀ ≤ Q := by
    have h1 : C ≤ h * ell := by
      calc C ≤ h := hCh
        _ = h * 1 := (mul_one h).symm
        _ ≤ h * ell := Nat.mul_le_mul_left h (by omega)
    exact le_trans hC_ge_Q0 h1
  obtain ⟨q₀, hq₀2, hq₀_le_Q, hQ_le_Cq, G₀, hExp₀, hLdeg₀, hRdeg₀, _hHall₀, hConn₀, hGirth₀⟩ :=
    h352 Q hQ_ge_Q0
  have hL2 : ∀ u, 2 ≤ (G₀ u).card := fun u => (hLdeg₀ u).1
  have hL16 : ∀ u, (G₀ u).card ≤ 16 := fun u => (hLdeg₀ u).2
  have hR2 : ∀ v, 2 ≤ (PEqualNP.Expanders.rightNbrs G₀ v).card := fun v => (hRdeg₀ v).1
  have hR16 : ∀ v, (PEqualNP.Expanders.rightNbrs G₀ v).card ≤ 16 := fun v => (hRdeg₀ v).2
  have hG1_cardLR := PEqualNP.Outside.L_pcx_355_aux.subcubic_card_LR G₀ hL2 hR2
  obtain ⟨hG1_degL, hG1_u0deg2, hG1_edges⟩ := PEqualNP.Outside.L_pcx_355_aux.subcubic_degL G₀ hL2 hR2
  obtain ⟨hG1_degR, hG1_r0deg2⟩ := PEqualNP.Outside.L_pcx_355_aux.subcubic_degR G₀ hL2 hR2
  have hG1_conn := PEqualNP.Outside.L_pcx_355_aux.subcubic_conn G₀ hL2 hR2 hConn₀
  let G₁ := PEqualNP.Outside.L_pcx_355_aux.G1 G₀
  let e₀ : ℕ := Fintype.card (PEqualNP.Expanders.GEdge G₀)
  let e₁ : ℕ := Fintype.card (PEqualNP.Outside.L_pcx_355_aux.GenEdge G₁)
  have he0_le : e₀ ≤ 16 * (q₀ + 1) := by
    change Fintype.card (PEqualNP.Expanders.GEdge G₀) ≤ 16 * (q₀ + 1)
    rw [PEqualNP.Outside.L_pcx_355_aux.card_GEdge_sum_L G₀]
    calc ∑ u : Fin (q₀ + 1), PEqualNP.Outside.L_pcx_355_aux.degL G₀ u
        ≤ ∑ _u : Fin (q₀ + 1), 16 := Finset.sum_le_sum (fun u _ => hL16 u)
      _ = 16 * (q₀ + 1) := by simp [mul_comm]
  have he0_ge : 2 * (q₀ + 1) ≤ e₀ := by
    change 2 * (q₀ + 1) ≤ Fintype.card (PEqualNP.Expanders.GEdge G₀)
    rw [PEqualNP.Outside.L_pcx_355_aux.card_GEdge_sum_L G₀]
    calc 2 * (q₀ + 1) = ∑ _u : Fin (q₀ + 1), 2 := by simp [mul_comm]
      _ ≤ ∑ u : Fin (q₀ + 1), PEqualNP.Outside.L_pcx_355_aux.degL G₀ u :=
          Finset.sum_le_sum (fun u _ => hL2 u)
  have he1_le_Q : e₁ ≤ 160 * Q := by
    have hq1 : q₀ + 1 ≤ 2 * q₀ := by omega
    have he0_le2 : e₀ ≤ 32 * Q :=
      calc e₀ ≤ 16 * (q₀ + 1) := he0_le
        _ ≤ 16 * (2 * q₀) := Nat.mul_le_mul_left 16 hq1
        _ ≤ 16 * (2 * Q) := Nat.mul_le_mul_left 16 (Nat.mul_le_mul_left 2 hq₀_le_Q)
        _ = 32 * Q := by ring
    have : e₁ = 5 * e₀ - 4 * q₀ - 2 := hG1_edges
    omega
  have he1_pos : 1 ≤ e₁ := by
    have : e₁ = 5 * e₀ - 4 * q₀ - 2 := hG1_edges
    omega
  have he1_le_ell : e₁ ≤ 160 * ell ^ 2 := by
    have hQ_le : Q ≤ ell ^ 2 := by
      calc h * ell ≤ ell * ell := Nat.mul_le_mul_right ell hhell
        _ = ell ^ 2 := by ring
    omega
  have h8e1_le_N : 8 * e₁ ≤ N := by omega
  let t : ℕ := N / (4 * e₁)
  have ht2 : 2 ≤ t := by
    rw [Nat.le_div_iff_mul_le (by omega : 0 < 4 * e₁)]
    omega
  have h4e1t_le : 4 * e₁ * t ≤ N := Nat.mul_div_le N (4 * e₁)
  have hN_lt_8te1 : N < 8 * t * e₁ := by
    have hlt : N < 4 * e₁ * (t + 1) := Nat.lt_mul_div_succ N (by omega : 0 < 4 * e₁)
    have : 4 * e₁ * (t + 1) ≤ 8 * t * e₁ :=
      calc 4 * e₁ * (t + 1) ≤ 4 * e₁ * (2 * t) := Nat.mul_le_mul_left (4 * e₁) (by omega)
        _ = 8 * t * e₁ := by ring
    omega
  have hL_le_3N : 4 * ((2 * t + 1) * e₁) ≤ 3 * N := by
    have h3 : 4 * ((2 * t + 1) * e₁) = 2 * (4 * e₁ * t) + 4 * e₁ := by ring
    omega
  let rem : ℕ := N - (2 * t + 1) * e₁
  have hN_le_4rem : N ≤ 4 * rem := by omega
  have hrem_ge4 : 4 ≤ rem := by
    have : 2 ^ 30 = 1073741824 := by norm_num
    omega
  have he1_card_pos : 0 < Fintype.card (PEqualNP.Outside.L_pcx_355_aux.GenEdge G₁) := by omega
  let ePick : PEqualNP.Outside.L_pcx_355_aux.GenEdge G₁ :=
    Classical.choice (Fintype.card_pos_iff.mp he1_card_pos)
  let earLen : ℕ := if rem % 2 = 0 then 0 else (rem - 1) / 2
  let s : PEqualNP.Outside.L_pcx_355_aux.GenEdge G₁ → ℕ :=
    fun e => if rem % 2 = 0 ∧ e = ePick then t + rem / 2 else t
  have hs_ge_t : ∀ e, t ≤ s e := by
    intro e; dsimp only [s]; split_ifs <;> omega
  have hs_ge_1 : ∀ e, 1 ≤ s e := fun e => le_trans (by omega) (hs_ge_t e)
  let u0 : Fin (q₀ + 1) := ⟨0, Nat.succ_pos q₀⟩
  let uStar : PEqualNP.Outside.L_pcx_355_aux.L1 G₀ :=
    Sum.inl ⟨u0, ⟨0, by have := hL2 u0; unfold PEqualNP.Outside.L_pcx_355_aux.degL; omega⟩⟩
  let vStar : PEqualNP.Outside.L_pcx_355_aux.R1 G₀ :=
    Sum.inr ⟨u0, ⟨0, by have := hL2 u0; unfold PEqualNP.Outside.L_pcx_355_aux.degL; omega⟩⟩
  have huStar_deg : (G₁ uStar).card = 2 := hG1_u0deg2 u0
  have hvStar_deg : (PEqualNP.Outside.L_pcx_355_aux.gRightNbrs G₁ vStar).card = 2 := hG1_r0deg2 u0
  let G₂ := PEqualNP.Outside.L_pcx_355_aux.G2 G₁ s earLen uStar vStar
  have hG2_cardLR := PEqualNP.Outside.L_pcx_355_aux.stretch_card_LR G₁ s earLen hG1_cardLR
  obtain ⟨hG2_degL, hG2_degR, hG2_edges_eq⟩ :=
    PEqualNP.Outside.L_pcx_355_aux.stretch_deg_and_edges G₁ s earLen uStar vStar
      hs_ge_1 hG1_degL hG1_degR (Or.inr huStar_deg) (Or.inr hvStar_deg)
  have hG2_conn := PEqualNP.Outside.L_pcx_355_aux.stretch_conn G₁ s earLen uStar vStar hs_ge_1 hG1_conn
  have hG2_edges : Fintype.card (PEqualNP.Outside.L_pcx_355_aux.GenEdge G₂) = N := by
    have he1_eq : ∀ i : Fintype (PEqualNP.Outside.L_pcx_355_aux.GenEdge G₁), @Fintype.card _ i = e₁ :=
      fun i => PEqualNP.Outside.L_pcx_355_aux.card_eq_of_fintype i _
    rw [hG2_edges_eq]
    by_cases hpar : rem % 2 = 0
    · have hear0 : earLen = 0 := by simp [earLen, hpar]
      simp only [hear0, lt_irrefl, ↓reduceIte, add_zero]
      have hsum : ∑ e : PEqualNP.Outside.L_pcx_355_aux.GenEdge G₁, (2 * s e + 1) =
          (∑ _e : PEqualNP.Outside.L_pcx_355_aux.GenEdge G₁, (2 * t + 1)) + 2 * (rem / 2) := by
        have hpt : ∀ e : PEqualNP.Outside.L_pcx_355_aux.GenEdge G₁,
            2 * s e + 1 = (2 * t + 1) + (if e = ePick then 2 * (rem / 2) else 0) := by
          intro e; dsimp only [s]; simp only [hpar, true_and]
          split_ifs <;> omega
        simp_rw [hpt, Finset.sum_add_distrib]
        simp
      rw [hsum]
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, he1_eq]
      have hmul : e₁ * (2 * t + 1) = (2 * t + 1) * e₁ := mul_comm _ _
      omega
    · have hear_eq : earLen = (rem - 1) / 2 := by simp [earLen, hpar]
      have hear_pos : 0 < earLen := by omega
      simp only [hear_pos, ↓reduceIte]
      have hpt : ∀ e : PEqualNP.Outside.L_pcx_355_aux.GenEdge G₁, 2 * s e + 1 = 2 * t + 1 := by
        intro e; dsimp only [s]; simp [hpar]
      simp_rw [hpt]
      simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, he1_eq]
      have hmul : e₁ * (2 * t + 1) = (2 * t + 1) * e₁ := mul_comm _ _
      omega
  have hG2_girth : ∀ (a : ℕ) (us : Fin (a + 2) ↪ PEqualNP.Outside.L_pcx_355_aux.L2 G₁ s earLen)
      (vs : Fin (a + 2) ↪ PEqualNP.Outside.L_pcx_355_aux.R2 G₁ s earLen),
      (∀ i, vs i ∈ G₂ (us i) ∧ vs i ∈ G₂ (us (i + 1))) →
      N * Nat.clog 2 (ell + 1) ≤ C * (2 * (a + 2)) * h * ell := by
    intro a us vs hcyc
    rcases PEqualNP.Outside.L_pcx_355_aux.stretch_girth G₁ s earLen uStar vStar t (by omega) hs_ge_t a us vs hcyc with
      ⟨hear_pos, hear_le⟩ | ⟨a₁, us₁, vs₁, hcount1, hcyc1⟩
    · have hpar : rem % 2 ≠ 0 := by
        intro hp; simp [earLen, hp] at hear_pos
      have hear_eq : earLen = (rem - 1) / 2 := by simp [earLen, hpar]
      have hN_le_ear : N ≤ 12 * earLen := by omega
      have hclog_le_ell : Nat.clog 2 (ell + 1) ≤ ell := by
        rw [Nat.clog_le_iff_le_pow (by omega : 1 < 2)]
        have : ell < 2 ^ ell := Nat.lt_two_pow_self
        omega
      have h1 : N * Nat.clog 2 (ell + 1) ≤ 6 * (2 * (a + 2)) * ell := by
        have hNa : N ≤ 6 * (2 * (a + 2)) := by omega
        exact Nat.mul_le_mul hNa hclog_le_ell
      have h2 : 6 * (2 * (a + 2)) * ell ≤ C * (2 * (a + 2)) * h * ell := by
        have h6C : 6 ≤ C * h :=
          le_trans (by decide : 6 ≤ 3 * 2) (Nat.mul_le_mul (by omega : 3 ≤ C) (by omega : 2 ≤ h))
        calc 6 * (2 * (a + 2)) * ell = (2 * (a + 2)) * ell * 6 := by ring
          _ ≤ (2 * (a + 2)) * ell * (C * h) := Nat.mul_le_mul_left _ h6C
          _ = C * (2 * (a + 2)) * h * ell := by ring
      exact le_trans h1 h2
    · obtain ⟨a₀, us₀, vs₀, ha0_le, hcyc0⟩ :=
        PEqualNP.Outside.L_pcx_355_aux.subcubic_girth G₀ a₁ us₁ vs₁ hcyc1
      have hg0 := hGirth₀ a₀ us₀ vs₀ hcyc0
      have hclog_le_Q : Nat.clog 2 (ell + 1) ≤ Nat.clog 2 Q := by
        apply Nat.clog_mono_right
        have : ell + 1 ≤ 2 * ell := by omega
        have : 2 * ell ≤ h * ell := Nat.mul_le_mul_right ell (by omega)
        omega
      have hclog_le_a1 : Nat.clog 2 (ell + 1) ≤ C₀ * (2 * (a₁ + 2)) := by
        calc Nat.clog 2 (ell + 1) ≤ Nat.clog 2 Q := hclog_le_Q
          _ ≤ C₀ * (2 * (a₀ + 2)) := hg0
          _ ≤ C₀ * (2 * (a₁ + 2)) := Nat.mul_le_mul_left C₀ (by omega)
      have hN_le : N ≤ 8 * t * (160 * h * ell) := by
        have h1 : 8 * t * e₁ ≤ 8 * t * (160 * Q) := Nat.mul_le_mul_left (8 * t) he1_le_Q
        have hQdef : 160 * Q = 160 * h * ell := by dsimp [Q]; ring
        rw [hQdef] at h1
        omega
      have h640C0 : 640 * C₀ ≤ C := by
        have : C₀ ≤ C₀ ^ 3 := Nat.le_self_pow (by decide : 3 ≠ 0) C₀
        omega
      calc N * Nat.clog 2 (ell + 1)
          ≤ (8 * t * (160 * h * ell)) * (C₀ * (2 * (a₁ + 2))) :=
            Nat.mul_le_mul hN_le hclog_le_a1
        _ = (640 * C₀) * (2 * (2 * (a₁ + 2) * t)) * h * ell := by ring
        _ ≤ C * (2 * (a + 2)) * h * ell := by
            have h1 : (640 * C₀) * (2 * (2 * (a₁ + 2) * t)) ≤ C * (2 * (a + 2)) :=
              Nat.mul_le_mul h640C0 (by omega)
            calc (640 * C₀) * (2 * (2 * (a₁ + 2) * t)) * h * ell
                = ((640 * C₀) * (2 * (2 * (a₁ + 2) * t))) * (h * ell) := by ring
              _ ≤ (C * (2 * (a + 2))) * (h * ell) := Nat.mul_le_mul_right (h * ell) h1
              _ = C * (2 * (a + 2)) * h * ell := by ring
  let q : ℕ := Fintype.card (PEqualNP.Outside.L_pcx_355_aux.R2 G₁ s earLen)
  obtain ⟨G, hG_edges, hG_degL, hG_degR, hG_conn, hG_girth, hG_sim⟩ :=
    PEqualNP.Outside.L_pcx_355_aux.relabel_genBip G₂ q hG2_cardLR rfl
      hG2_degL hG2_degR hG2_conn (fun m => N * Nat.clog 2 (ell + 1) ≤ C * m * h * ell) hG2_girth
  refine ⟨q, G, hG_edges.trans ((PEqualNP.Outside.L_pcx_355_aux.card_eq_of_fintype _ _).trans hG2_edges), hG_degL, hG_degR, hG_conn, hG_girth, ?_⟩
  intro k d hk hd hCkd
  refine ⟨PEqualNP.ProofComplexity.L055 k (q + 1) q G hk (by omega), ?_⟩
  intro π hπ
  obtain ⟨π₂, hπ₂, hlen₂⟩ := hG_sim k π hk hπ
  obtain ⟨π₁, hπ₁, hlen₁⟩ := PEqualNP.Outside.L_pcx_355_aux.stretch_sim G₁ s earLen uStar vStar hs_ge_1 k hk π₂
    (PEqualNP.Outside.L_pcx_355_aux.isLinKRefutation_genGraphPHP_cast _ _ _ _ _ _ _ _ G₂ _ _ k π₂ hπ₂)
  obtain ⟨π₀, hπ₀, hlen₀⟩ := PEqualNP.Outside.L_pcx_355_aux.subcubic_sim G₀ hL2 hR2 hL16 hR16 k hk π₁
    (PEqualNP.Outside.L_pcx_355_aux.isLinKRefutation_genGraphPHP_cast _ _ _ _ _ _ _ _ G₁ _ _ k π₁ hπ₁)
  have hlen_tot : π₀.length ≤ 4800 * π.length + 4800 := by omega
  have hExp₀' : PEqualNP.Expanders.IsBdryExpander G₀ (q₀ / C₀) 2 := by
    intro S hS
    exact hExp₀ S (le_trans hS (Nat.div_le_div_right hq₀_le_Q))
  have hL : PEqualNP.ProofComplexity.LinKFinal.StmtLinK :=
    PEqualNP.ProofComplexity.LinKWire.general PEqualNP.ProofComplexity.LinKSim.simulation_refutation
  exact PEqualNP.Outside.L_pcx_355_aux.final_bound_355 C₀ C q₀ k d ell N h π₀.length π.length
    hC₀2 hC2 hC_ge_B hCh hell30 hN_le_pow hQ_le_Cq hk hd hCkd hlen_tot
    (fun hn1 hn2 => PEqualNP.ProofComplexity.LinKGrow.graph_bound hL 16 C₀ q₀ k 16 rfl (by omega) hk
      G₀ hL16 hExp₀' hn1 hn2 π₀ hπ₀)
