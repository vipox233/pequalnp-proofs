import Mathlib
import PEqualNP.Defs

/-!
L-lib-1210.

Reduction layer: a marked graph is produced from a directed implication relation `E` on `Fin m`
(out-degree and in-degree at most two, irreflexive): the false copy of `i` is joined to the true
copy of `i` and to the true copies of the out-neighbours of `i`; the true copy of `i` is joined to
the false copies of its in-neighbours.  With `v i := x (i,true)` the marked covers are exactly the
assignments `v` with `v i = true` for inactive `i` and `v i -> v j` along every edge `i -> j`
leaving an active vertex (`cover_count`), so `0 < Z` always (`cover_pos`).  `of_cons` derives the
statement from a `Cons n k q` (implication relation, sources, intervals and the count).

The graph (`Vx n k M`, edges `outN`): levels are directed 4-cycles a -> b -> b2 -> c -> a (tracks
and rings) or 3-cycles (counter chains), consecutive levels joined by c <-> a.
* track of variable i: levels t <= k; port b of level e for the positive literal of clause e,
  port b2 for its negation gadget.
* ring of clause e: levels t <= n; port b of level i receives the positive literal, b2 the
  negative one, port b of level n is joined both ways to the top of the clause counter.
* literal vertex Lt e i b (source (e,i,b)): positive one joined both ways to the track port and
  pointing to the ring; negative one joined both ways to the negation vertex N e i.
* negation gadget: N e i and two counter chains of value 2^L q + q - 1, one fed by the track port
  and N, the other with every edge reversed feeding them; the pair counts 0 mod q when N equals
  the variable and 1 otherwise.
* clause counter: chain of value 2^L q + code (stoppers sourced by the bits of code).
Count (`count_main`): `closed_iff` splits a cover into constant tracks and rings (interface) and
independent blocks, `card_split` sums block counts, `reindex` passes to (y, tau, nu), and the
algebra in `ZMod q` (`alg_main`, `clause_val`) gives the clause factors.
Path decomposition: intervals `lo`, `hi` through `enc`; `edge_ok`, `width` (at most n + 11 vertices
alive: one carried vertex per track and a list of at most eleven local vertices).
-/

namespace PEqualNP.Outside.L_lib_1210_aux

open Finset

/-- The marked graph of an implication relation. -/
def nbOf {m : ℕ} (E : Fin m → Fin m → Bool) (p : Fin m × Bool) : Finset (Fin m × Bool) :=
  if p.2 then insert (p.1, false) ((univ.filter (fun j => E j p.1 = true)).image (fun j => (j, false)))
  else insert (p.1, true) ((univ.filter (fun j => E p.1 j = true)).image (fun j => (j, true)))

lemma mem_nbOf_false_true {m : ℕ} (E : Fin m → Fin m → Bool) (i j : Fin m) :
    (j, true) ∈ nbOf E (i, false) ↔ (j = i ∨ E i j = true) := by
  simp [nbOf]

lemma mem_nbOf_true_false {m : ℕ} (E : Fin m → Fin m → Bool) (i j : Fin m) :
    (j, false) ∈ nbOf E (i, true) ↔ (j = i ∨ E j i = true) := by
  simp [nbOf]

lemma not_mem_nbOf_same {m : ℕ} (E : Fin m → Fin m → Bool) (i j : Fin m) (a : Bool) :
    (j, a) ∉ nbOf E (i, a) := by
  cases a <;> simp [nbOf]

lemma mem_nbOf_iff {m : ℕ} (E : Fin m → Fin m → Bool) (p r : Fin m × Bool) :
    r ∈ nbOf E p ↔ (p.2 = false ∧ r.2 = true ∧ (r.1 = p.1 ∨ E p.1 r.1 = true)) ∨
      (p.2 = true ∧ r.2 = false ∧ (r.1 = p.1 ∨ E r.1 p.1 = true)) := by
  obtain ⟨i, a⟩ := p
  obtain ⟨j, b⟩ := r
  cases a <;> cases b
  · simp only [not_mem_nbOf_same, false_iff]; simp
  · rw [mem_nbOf_false_true]; simp
  · rw [mem_nbOf_true_false]; simp
  · simp only [not_mem_nbOf_same, false_iff]; simp

lemma card_nbOf_le {m : ℕ} (E : Fin m → Fin m → Bool)
    (hout : ∀ i, (univ.filter (fun j => E i j = true)).card ≤ 2)
    (hin : ∀ j, (univ.filter (fun i => E i j = true)).card ≤ 2) (p : Fin m × Bool) :
    (nbOf E p).card ≤ 3 := by
  obtain ⟨i, a⟩ := p
  cases a
  · simp only [nbOf, Bool.false_eq_true, ↓reduceIte]
    calc _ ≤ _ + 1 := card_insert_le _ _
      _ ≤ (univ.filter (fun j => E i j = true)).card + 1 := by gcongr; exact card_image_le
      _ ≤ 3 := by have := hout i; omega
  · simp only [nbOf, ↓reduceIte]
    calc _ ≤ _ + 1 := card_insert_le _ _
      _ ≤ (univ.filter (fun j => E j i = true)).card + 1 := by gcongr; exact card_image_le
      _ ≤ 3 := by have := hin i; omega

/-- Marked covers with prescribed activity are implication-closed assignments. -/
lemma cover_count {m : ℕ} (E : Fin m → Fin m → Bool) (act : Fin m → Bool)
    [DecidablePred (fun x : Fin m × Bool → Bool =>
      (∀ p, ∀ r ∈ nbOf E p, x p = true ∨ x r = true) ∧ ∀ i, xor (x (i,false)) (x (i,true)) = act i)] :
    (univ.filter (fun x : Fin m × Bool → Bool =>
      (∀ p, ∀ r ∈ nbOf E p, x p = true ∨ x r = true) ∧
        ∀ i, xor (x (i,false)) (x (i,true)) = act i)).card =
    (univ.filter (fun v : Fin m → Bool => (∀ i, act i = false → v i = true) ∧
        ∀ i j, E i j = true → act i = true → v i = true → v j = true)).card := by
  apply card_nbij' (fun x i => x (i, true))
    (fun v p => if p.2 then v p.1 else xor (act p.1) (v p.1))
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
    obtain ⟨hc, hxor⟩ := hx
    refine ⟨fun i hi => ?_, fun i j hij hai hvi => ?_⟩
    · have h1 := hc (i, false) (i, true) ((mem_nbOf_false_true E i i).2 (Or.inl rfl))
      have h2 := hxor i
      rw [hi] at h2
      cases h3 : x (i, false) <;> cases h4 : x (i, true) <;> simp_all
    · have h1 := hc (i, false) (j, true) ((mem_nbOf_false_true E i j).2 (Or.inr hij))
      have h2 := hxor i
      rw [hai] at h2
      cases h3 : x (i, false) <;> cases h4 : x (i, true) <;> simp_all
  · intro v hv
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv ⊢
    obtain ⟨hin, himp⟩ := hv
    refine ⟨fun p r hr => ?_, fun i => ?_⟩
    · rw [mem_nbOf_iff] at hr
      obtain ⟨i, a⟩ := p
      obtain ⟨j, b⟩ := r
      rcases hr with ⟨ha, hb, hr⟩ | ⟨ha, hb, hr⟩
      · simp only at ha hb hr
        subst ha; subst hb
        simp only [Bool.false_eq_true, ↓reduceIte]
        rcases hr with rfl | hr
        · cases h1 : act j <;> cases h2 : v j <;> simp_all
        · have hh := himp i j hr
          cases h1 : act i <;> cases h2 : v i <;> cases h3 : v j <;> simp_all
      · simp only at ha hb hr
        subst ha; subst hb
        simp only [Bool.false_eq_true, ↓reduceIte]
        rcases hr with rfl | hr
        · cases h1 : act j <;> cases h2 : v j <;> simp_all
        · have hh := himp j i hr
          cases h1 : act j <;> cases h2 : v j <;> cases h3 : v i <;> simp_all
    · simp
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
    funext p
    obtain ⟨i, a⟩ := p
    cases a
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have := hx.2 i
      cases h3 : x (i, false) <;> cases h4 : x (i, true) <;> cases h5 : act i <;> simp_all
    · simp
  · intro v _
    funext i
    simp

lemma cover_pos {m : ℕ} (E : Fin m → Fin m → Bool) (act : Fin m → Bool) :
    0 < (univ.filter (fun v : Fin m → Bool => (∀ i, act i = false → v i = true) ∧
        ∀ i j, E i j = true → act i = true → v i = true → v j = true)).card := by
  apply card_pos.2
  exact ⟨fun _ => true, by simp⟩

/-! ### Counting lemmas -/


lemma card_split {I B : Type*} {W : B → Type*} [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B]
    [∀ b, Fintype (W b)] [∀ b, DecidableEq (W b)]
    (PI : (I → Bool) → Prop) [DecidablePred PI]
    (PB : ∀ b, (I → Bool) → (W b → Bool) → Prop) [∀ b σ, DecidablePred (PB b σ)]
    [DecidablePred (fun v : I ⊕ (Σ b, W b) → Bool =>
      PI (fun i => v (Sum.inl i)) ∧ ∀ b, PB b (fun i => v (Sum.inl i)) (fun w => v (Sum.inr ⟨b, w⟩)))] :
    (univ.filter (fun v : I ⊕ (Σ b, W b) → Bool =>
      PI (fun i => v (Sum.inl i)) ∧ ∀ b, PB b (fun i => v (Sum.inl i)) (fun w => v (Sum.inr ⟨b, w⟩)))).card =
    ∑ σ : I → Bool, if PI σ then ∏ b, (univ.filter (PB b σ)).card else 0 := by
  rw [card_filter]
  let e : (I → Bool) × (∀ b, W b → Bool) ≃ (I ⊕ (Σ b, W b) → Bool) :=
    (Equiv.prodCongr (Equiv.refl _) (Equiv.piCurry (fun b (_ : W b) => Bool)).symm).trans
      (Equiv.sumArrowEquivProdArrow _ _ _).symm
  rw [← e.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  by_cases h : PI σ
  · simp only [card_filter]
    rw [if_pos h, Fintype.prod_sum]
    refine Finset.sum_congr rfl (fun f _ => ?_)
    rw [Fintype.prod_boole]
    simp [e, h, Sigma.uncurry]
  · rw [if_neg h]
    refine Finset.sum_eq_zero (fun f _ => ?_)
    simp [e, h]


/-- Weight of one counter transition between consecutive level values `a` (lower) and `b`
(upper), after the stopper and the pendant are summed out. -/
def chainG (off a b : Bool) : ℕ :=
  match a, b with
  | true, true => 1
  | false, false => 2
  | true, false => if off then 1 else 0
  | false, true => 0

/-- Leading one followed by the transition modes, most significant first. -/
def chainVal : ℕ → (ℕ → Bool) → ℕ
  | 0, _ => 1
  | M+1, off => 2 * chainVal M off + (if off M then 1 else 0)

lemma chain_sum (off : ℕ → Bool) : ∀ (M : ℕ) (τ : Bool),
    ∑ v : Fin (M+1) → Bool, (if v (Fin.last M) = τ then 1 else 0) *
      ∏ j : Fin M, chainG (off j) (v j.castSucc) (v j.succ) = if τ then 1 else chainVal M off
  | 0, τ => by
    rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp, Fintype.sum_bool]
    cases τ <;> simp [chainVal]
  | M+1, τ => by
    rw [← (Fin.snocEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type]
    have key : ∀ (b : Bool) (μ : Fin (M+1) → Bool),
        (if (Fin.snocEquiv (fun _ => Bool)) (b, μ) (Fin.last (M+1)) = τ then 1 else 0) *
          ∏ j : Fin (M+1), chainG (off j) ((Fin.snocEquiv (fun _ => Bool)) (b, μ) j.castSucc)
            ((Fin.snocEquiv (fun _ => Bool)) (b, μ) j.succ) =
        (if b = τ then 1 else 0) * ((∏ j : Fin M, chainG (off j) (μ j.castSucc) (μ j.succ)) *
          chainG (off M) (μ (Fin.last M)) b) := by
      intro b μ
      simp only [Fin.snocEquiv_apply, Fin.snoc_last]
      rw [Fin.prod_univ_castSucc]
      congr 2
      · refine Finset.prod_congr rfl (fun j _ => ?_)
        have : (j.castSucc.succ : Fin (M+2)) = (j.succ).castSucc := rfl
        rw [this, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.coe_castSucc]
      · have : ((Fin.last M).succ : Fin (M+2)) = Fin.last (M+1) := rfl
        simp [this, Fin.snoc_castSucc]
    simp_rw [key]
    have h2 : ∀ μ : Fin (M+1) → Bool,
        (∏ j : Fin M, chainG (off j) (μ j.castSucc) (μ j.succ)) * chainG (off M) (μ (Fin.last M)) τ =
        ∑ a : Bool, chainG (off M) a τ * ((if μ (Fin.last M) = a then 1 else 0) *
          ∏ j : Fin M, chainG (off j) (μ j.castSucc) (μ j.succ)) := by
      intro μ
      rw [Fintype.sum_bool]
      cases μ (Fin.last M) <;> simp [mul_comm]
    calc _ = ∑ μ : Fin (M+1) → Bool,
          (∏ j : Fin M, chainG (off j) (μ j.castSucc) (μ j.succ)) * chainG (off M) (μ (Fin.last M)) τ := by
            rw [Fintype.sum_bool]; cases τ <;> simp
      _ = ∑ a : Bool, chainG (off M) a τ * ∑ μ : Fin (M+1) → Bool, (if μ (Fin.last M) = a then 1 else 0) *
            ∏ j : Fin M, chainG (off j) (μ j.castSucc) (μ j.succ) := by
            simp_rw [h2]; rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
      _ = _ := by
            simp_rw [chain_sum off M]
            rw [Fintype.sum_bool]
            cases τ <;> simp [chainG, chainVal] <;> omega

lemma chainVal_horner (off : ℕ → Bool) (M : ℕ) : ∀ (L c : ℕ), c < 2^L →
    (∀ j < L, off (M + j) = c.testBit (L - 1 - j)) →
    chainVal (M + L) off = 2^L * chainVal M off + c
  | 0, c, hc, _ => by simp at hc; subst hc; simp
  | L+1, c, hc, hoff => by
    have hc2 : c / 2 < 2^L := by
      rw [Nat.div_lt_iff_lt_mul (by norm_num)]; rw [pow_succ] at hc; exact hc
    have ih := chainVal_horner off M L (c / 2) hc2 (fun j hj => by
      rw [hoff j (by omega), Nat.testBit_div_two]; congr 1; omega)
    rw [show M + (L+1) = (M + L) + 1 by ring, chainVal, ih, hoff L (by omega)]
    simp only [show L + 1 - 1 - L = 0 by omega, Nat.testBit_zero]
    have e1 : 2 ^ (L+1) * chainVal M off = 2 * (2^L * chainVal M off) := by ring
    rw [e1]
    have := Nat.div_add_mod c 2
    rcases Nat.mod_two_eq_zero_or_one c with h | h <;> simp [h] <;> omega

/-- Stopper constraint: present stoppers sit between the lower level and either the same level
(off) or the upper level (on); an absent stopper is forced true. -/
def stopOK (pres off : Bool) (c b a u : Bool) : Prop :=
  if pres = true then (c = true → u = true) ∧ (u = true → (if off = true then b else a) = true)
  else u = true

instance (pres off c b a u : Bool) : Decidable (stopOK pres off c b a u) := by
  unfold stopOK; infer_instance

abbrev ChainV (M : ℕ) := (Fin (M+1) × Fin 3) ⊕ (Σ _ : Fin M ⊕ Fin M, Unit)

def chainPI (M : ℕ) (τ : Bool) (σ : Fin (M+1) × Fin 3 → Bool) : Prop :=
  (∀ j : Fin (M+1), (σ (j,0) = true → σ (j,1) = true) ∧ (σ (j,1) = true → σ (j,2) = true) ∧
      (σ (j,2) = true → σ (j,0) = true)) ∧
    (∀ j : Fin M, σ (j.succ, 0) = true → σ (j.castSucc, 2) = true) ∧ σ (Fin.last M, 1) = τ

def chainPB (M : ℕ) (pres off : ℕ → Bool) :
    ∀ b : Fin M ⊕ Fin M, (Fin (M+1) × Fin 3 → Bool) → (Unit → Bool) → Prop
  | Sum.inl j, σ, w => stopOK (pres j) (off j) (σ (j.castSucc, 2)) (σ (j.castSucc, 1)) (σ (j.succ, 0)) (w ())
  | Sum.inr j, σ, w => σ (j.castSucc, 1) = true → w () = true

instance (M : ℕ) (pres off : ℕ → Bool) (b : Fin M ⊕ Fin M) (σ : Fin (M+1) × Fin 3 → Bool) :
    DecidablePred (chainPB M pres off b σ) := by
  intro w; cases b <;> unfold chainPB <;> infer_instance

lemma card_unit_fun (P : Bool → Prop) [DecidablePred P] :
    (univ.filter (fun w : Unit → Bool => P (w ()))).card =
      (if P true then 1 else 0) + (if P false then 1 else 0) := by
  rw [card_filter, ← (Equiv.funUnique Unit Bool).symm.sum_comp, Fintype.sum_bool]
  simp [add_comm]

lemma step_eq (pres off l0 l1 : Bool) :
    (if l1 = true → l0 = true then 1 else 0) *
      ((univ.filter (fun w : Unit → Bool => stopOK pres off l0 l0 l1 (w ()))).card *
        (univ.filter (fun w : Unit → Bool => l0 = true → w () = true)).card) =
    chainG (off || !pres) l0 l1 := by
  rw [card_unit_fun (fun u => stopOK pres off l0 l0 l1 u), card_unit_fun (fun u => l0 = true → u = true)]
  cases pres <;> cases off <;> cases l0 <;> cases l1 <;> simp [stopOK, chainG]

lemma chain_count (M : ℕ) (pres off : ℕ → Bool) (τ : Bool)
    [DecidablePred (fun v : ChainV M → Bool => chainPI M τ (fun i => v (Sum.inl i)) ∧
      ∀ b, chainPB M pres off b (fun i => v (Sum.inl i)) (fun w => v (Sum.inr ⟨b, w⟩)))] :
    (univ.filter (fun v : ChainV M → Bool => chainPI M τ (fun i => v (Sum.inl i)) ∧
      ∀ b, chainPB M pres off b (fun i => v (Sum.inl i)) (fun w => v (Sum.inr ⟨b, w⟩)))).card =
    if τ then 1 else chainVal M (fun j => off j || !pres j) := by
  classical
  rw [card_split, ← chain_sum (fun j => off j || !pres j) M τ]
  rw [← Finset.sum_filter]
  let lift : (Fin (M+1) → Bool) → (Fin (M+1) × Fin 3 → Bool) := fun l p => l p.1
  have hconst : ∀ σ, chainPI M τ σ → lift (fun j => σ (j, 1)) = σ := by
    intro σ h
    funext p
    obtain ⟨j, r⟩ := p
    obtain ⟨h1, h2, h3⟩ := h.1 j
    show σ (j, 1) = σ (j, r)
    fin_cases r
    · cases e0 : σ (j, 0) <;> cases e1 : σ (j, 1) <;> cases e2 : σ (j, 2) <;> simp_all
    · rfl
    · cases e0 : σ (j, 0) <;> cases e1 : σ (j, 1) <;> cases e2 : σ (j, 2) <;> simp_all
  rw [Finset.sum_nbij' (fun σ => fun j => σ (j, 1)) lift
    (t := univ.filter (fun l : Fin (M+1) → Bool => chainPI M τ (lift l)))
    (g := fun l => ∏ b, (univ.filter (chainPB M pres off b (lift l))).card)]
  · rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    have hPI : chainPI M τ (lift l) ↔
        (∀ j : Fin M, l j.succ = true → l j.castSucc = true) ∧ l (Fin.last M) = τ := by
      simp [chainPI, lift]
    rw [Fintype.prod_sum_type]
    by_cases hl : (∀ j : Fin M, l j.succ = true → l j.castSucc = true)
    · by_cases ht : l (Fin.last M) = τ
      · rw [if_pos (hPI.2 ⟨hl, ht⟩), if_pos ht, one_mul, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl (fun j _ => ?_)
        rw [← step_eq (pres j) (off j) (l j.castSucc) (l j.succ), if_pos (hl j), one_mul]
        rfl
      · rw [if_neg (fun h => ht (hPI.1 h).2), if_neg ht, zero_mul]
    · rw [if_neg (fun h => hl (hPI.1 h).1)]
      symm
      rcases (by push_neg at hl; exact hl) with ⟨j, hj1, hj2⟩
      apply mul_eq_zero_of_right
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      rw [← step_eq (pres j) (off j) (l j.castSucc) (l j.succ)]
      simp [hj1, hj2]
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ ⊢
    rw [hconst σ hσ]; exact hσ
  · intro l hl
    simpa using hl
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ
    exact hconst σ hσ
  · intro l _
    rfl
  · intro σ hσ
    simp only [mem_filter, mem_univ, true_and] at hσ
    rw [hconst σ hσ]

lemma chainVal_congr (off off' : ℕ → Bool) : ∀ M, (∀ j < M, off j = off' j) →
    chainVal M off = chainVal M off'
  | 0, _ => rfl
  | M+1, h => by
    simp only [chainVal]
    rw [chainVal_congr off off' M (fun j hj => h j (by omega)), h M (by omega)]

/-- A chain whose modes are the bits of `x` below its leading one counts `x`. -/
lemma chainVal_bits (x : ℕ) (hx : x ≠ 0) (off : ℕ → Bool)
    (hoff : ∀ j < Nat.log2 x, off j = x.testBit (Nat.log2 x - 1 - j)) :
    chainVal (Nat.log2 x) off = x := by
  have h1 := Nat.log2_self_le hx
  have h2 := Nat.lt_log2_self (n := x)
  have hc : x % 2^(Nat.log2 x) < 2^(Nat.log2 x) := Nat.mod_lt _ (by positivity)
  have hh := chainVal_horner off 0 (Nat.log2 x) (x % 2^(Nat.log2 x)) hc (fun j hj => by
    have hlt : Nat.log2 x - 1 - j < Nat.log2 x := by omega
    rw [zero_add, hoff j hj, Nat.testBit_mod_two_pow]
    simp [hlt])
  rw [zero_add] at hh
  rw [hh]
  simp only [chainVal, mul_one]
  have hdiv : x / 2^(Nat.log2 x) = 1 := by
    apply le_antisymm
    · have : x / 2^(Nat.log2 x) < 2 := by
        rw [Nat.div_lt_iff_lt_mul (by positivity)]
        rw [pow_succ] at h2
        rw [mul_comm]; exact h2
      omega
    · exact (Nat.le_div_iff_mul_le (by positivity)).2 (by simpa using h1)
  have := Nat.div_add_mod x (2^(Nat.log2 x))
  rw [hdiv, mul_one] at this
  omega

/-- The clause counter: `q` read off its own bits, then the `L` bits of `code`. -/
lemma counter_val (q code : ℕ) (hq : 2 ≤ q) (hc : code < 2^(Nat.log2 q + 1)) (off : ℕ → Bool)
    (hlow : ∀ j < Nat.log2 q, off j = q.testBit (Nat.log2 q - 1 - j))
    (hhigh : ∀ j < Nat.log2 q + 1, off (Nat.log2 q + j) = code.testBit (Nat.log2 q + 1 - 1 - j)) :
    chainVal (Nat.log2 q + (Nat.log2 q + 1)) off = 2^(Nat.log2 q + 1) * q + code := by
  rw [chainVal_horner off (Nat.log2 q) (Nat.log2 q + 1) code hc hhigh,
    chainVal_bits q (by omega) off hlow]

/-- Everything the final statement needs, phrased on an implication relation and intervals. -/
structure Cons (n k q : ℕ) where
  m : ℕ
  E : Fin m → Fin m → Bool
  source : Fin m → Option ((Fin k × Fin n × Bool) ⊕ (Fin k × Fin (Nat.log2 q + 1)))
  lo : Fin m → ℕ
  hi : Fin m → ℕ
  l : ℕ
  size : m ≤ 200*(n+1)*(k+1)*((Nat.log2 q + 1)+1)
  irrefl : ∀ i, E i i = false
  outdeg : ∀ i, (univ.filter (fun j => E i j = true)).card ≤ 2
  indeg : ∀ j, (univ.filter (fun i => E i j = true)).card ≤ 2
  len : l ≤ 2*m+1
  lohi : ∀ i, lo i ≤ hi i
  hil : ∀ i, hi i < l
  edge : ∀ i j, E i j = true → lo i ≤ hi j ∧ lo j ≤ hi i
  width : ∀ t, (univ.filter (fun i => lo i ≤ t ∧ t ≤ hi i)).card ≤ n + 11
  count : ∀ (lit : Fin k → Fin n → Bool → Bool) (weight : Fin k → Fin q),
    (univ.filter (fun v : Fin m → Bool =>
      (∀ i, (source i).elim true (Sum.elim (fun p => lit p.1 p.2.1 p.2.2)
          (fun p => !((((weight p.1).val + q - 1) % q).testBit p.2.val))) = false → v i = true) ∧
      ∀ i j, E i j = true →
        (source i).elim true (Sum.elim (fun p => lit p.1 p.2.1 p.2.2)
          (fun p => !((((weight p.1).val + q - 1) % q).testBit p.2.val))) = true →
        v i = true → v j = true)).card % q =
    (∑ y : Fin n → Bool, ∏ e : Fin k,
      if ∀ i, lit e i (y i) = false then (weight e).val else 1) % q

theorem of_cons (H : ∀ n k q : ℕ, 2 ≤ q → Nonempty (Cons n k q)) :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    ∀ n k q : Nat, 2 ≤ q →
    let L := Nat.log2 q + 1
    ∃ (m : Nat) (nb : (Fin m × Bool) → Finset (Fin m × Bool))
      (source : Fin m → Option ((Fin k × Fin n × Bool) ⊕ (Fin k × Fin L))),
      m ≤ 200*(n+1)*(k+1)*(L+1) ∧
      (∀ p, p ∉ nb p ∧ (nb p).card ≤ 3) ∧
      (∀ p r, r ∈ nb p ↔ p ∈ nb r) ∧ (∀ p, ∀ r ∈ nb p, p.2 ≠ r.2) ∧
      (∀ i, (i,true) ∈ nb (i,false)) ∧
      (∃ (l : Nat) (bag : Fin l → Finset (Fin m)),
        l ≤ 2*m+1 ∧ (∀ t, (bag t).card ≤ n+11) ∧ (∀ i, ∃ t, i ∈ bag t) ∧
        (∀ i j, i ≠ j → (∃ a b : Bool, (j,b) ∈ nb (i,a)) →
          ∃ t, i ∈ bag t ∧ j ∈ bag t) ∧
        ∀ i s t u, s ≤ t → t ≤ u → i ∈ bag s → i ∈ bag u → i ∈ bag t) ∧
      ∀ (lit : Fin k → Fin n → Bool → Bool) (weight : Fin k → Fin q),
        let code := fun e => ((weight e).val + q - 1) % q
        let active := fun i => (source i).elim true (Sum.elim
          (fun p => lit p.1 p.2.1 p.2.2)
          (fun p => !((code p.1).testBit p.2.val)))
        let Z := ((Finset.univ : Finset ((Fin m × Bool) → Bool)).filter (fun x =>
          (∀ p, ∀ r ∈ nb p, x p = true ∨ x r = true) ∧
          ∀ i, xor (x (i,false)) (x (i,true)) = active i)).card
        let factor := fun (y : Fin n → Bool) (e : Fin k) =>
          if ∀ i, lit e i (y i) = false then (weight e).val else 1
        0 < Z ∧ Z % q = (∑ y : Fin n → Bool, ∏ e : Fin k, factor y e) % q := by
  intro n k q hq L
  obtain ⟨C⟩ := H n k q hq
  refine ⟨C.m, nbOf C.E, C.source, C.size, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    refine ⟨?_, card_nbOf_le C.E C.outdeg C.indeg p⟩
    obtain ⟨i, a⟩ := p
    exact not_mem_nbOf_same C.E i i a
  · intro p r
    rw [mem_nbOf_iff, mem_nbOf_iff]
    constructor
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
      · exact Or.inr ⟨h2, h1, h3.imp Eq.symm id⟩
      · exact Or.inl ⟨h2, h1, h3.imp Eq.symm id⟩
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
      · exact Or.inr ⟨h2, h1, h3.imp Eq.symm id⟩
      · exact Or.inl ⟨h2, h1, h3.imp Eq.symm id⟩
  · intro p r hr
    rw [mem_nbOf_iff] at hr
    rcases hr with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> rw [h1, h2] <;> decide
  · intro i
    exact (mem_nbOf_false_true C.E i i).2 (Or.inl rfl)
  · refine ⟨C.l, fun t => univ.filter (fun i => C.lo i ≤ t.val ∧ t.val ≤ C.hi i), C.len,
      fun t => ?_, fun i => ?_, fun i j hij hadj => ?_, fun i s t u hst htu hs hu => ?_⟩
    · convert C.width t.val
    · refine ⟨⟨C.lo i, lt_of_le_of_lt (C.lohi i) (C.hil i)⟩, ?_⟩
      simp [C.lohi i]
    · obtain ⟨a, b, hab⟩ := hadj
      rw [mem_nbOf_iff] at hab
      have hE : C.E i j = true ∨ C.E j i = true := by
        rcases hab with ⟨_, _, h | h⟩ | ⟨_, _, h | h⟩
        · exact absurd h.symm hij
        · exact Or.inl h
        · exact absurd h.symm hij
        · exact Or.inr h
      have h2 : C.lo i ≤ C.hi j ∧ C.lo j ≤ C.hi i := by
        rcases hE with h | h
        · exact C.edge i j h
        · exact (C.edge j i h).symm
      refine ⟨⟨max (C.lo i) (C.lo j), ?_⟩, ?_, ?_⟩
      · have := C.hil i; have := C.lohi i; have := C.lohi j; omega
      · simp only [mem_filter, mem_univ, true_and]
        have := C.lohi i; have := C.lohi j; omega
      · simp only [mem_filter, mem_univ, true_and]
        have := C.lohi i; have := C.lohi j; omega
    · simp only [mem_filter, mem_univ, true_and] at hs hu ⊢
      have : s.val ≤ t.val := hst
      have : t.val ≤ u.val := htu
      omega
  · intro lit weight code active Z factor
    have hZ : Z = (univ.filter (fun v : Fin C.m → Bool => (∀ i, active i = false → v i = true) ∧
        ∀ i j, C.E i j = true → active i = true → v i = true → v j = true)).card := by
      simp only [Z]
      convert cover_count C.E active
    refine ⟨?_, ?_⟩
    · rw [hZ]; exact cover_pos C.E active
    · rw [hZ]
      have := C.count lit weight
      convert this using 2
      apply Finset.sum_congr (by congr; exact Subsingleton.elim _ _)
      intro y _
      apply Finset.prod_congr rfl
      intro e _
      dsimp only [factor]
      split_ifs <;> tauto

inductive R3
  | a | b | c
  deriving DecidableEq

inductive R4
  | a | b | b2 | c
  deriving DecidableEq

instance : Fintype R3 := ⟨{.a, .b, .c}, by intro x; cases x <;> simp⟩
instance : Fintype R4 := ⟨{.a, .b, .b2, .c}, by intro x; cases x <;> simp⟩

def R3.toFin : R3 → Fin 3
  | .a => 0
  | .b => 1
  | .c => 2

def R3.ofFin (r : Fin 3) : R3 := if r = 0 then .a else if r = 1 then .b else .c

inductive CV (M : ℕ)
  | lev : Fin (M+1) → R3 → CV M
  | stp : Fin M → CV M
  | pnd : Fin M → CV M
  deriving DecidableEq

def cvEquiv (M : ℕ) : CV M ≃ ChainV M where
  toFun x := match x with
    | .lev j r => Sum.inl (j, r.toFin)
    | .stp j => Sum.inr ⟨Sum.inl j, ()⟩
    | .pnd j => Sum.inr ⟨Sum.inr j, ()⟩
  invFun x := match x with
    | Sum.inl (j, r) => .lev j (R3.ofFin r)
    | Sum.inr ⟨Sum.inl j, _⟩ => .stp j
    | Sum.inr ⟨Sum.inr j, _⟩ => .pnd j
  left_inv x := by
    cases x with
    | lev j r => cases r <;> rfl
    | stp j => rfl
    | pnd j => rfl
  right_inv x := by
    rcases x with ⟨j, r⟩ | ⟨j | j, ⟨⟩⟩
    · fin_cases r <;> rfl
    · rfl
    · rfl

instance (M : ℕ) : Fintype (CV M) := Fintype.ofEquiv _ (cvEquiv M).symm

def topB (M : ℕ) : CV M := .lev (Fin.last M) .b
def topC (M : ℕ) : CV M := .lev (Fin.last M) .c

def chainOut (M : ℕ) (off : ℕ → Bool) : CV M → Finset (CV M)
  | .lev j .a =>
      if h : 0 < j.val then {.lev j .b, .lev ⟨j.val - 1, by have := j.isLt; omega⟩ .c} else {.lev j .b}
  | .lev j .b => if h : j.val < M then {.lev j .c, .pnd ⟨j.val, h⟩} else {.lev j .c}
  | .lev j .c => if h : j.val < M then {.lev j .a, .stp ⟨j.val, h⟩} else {.lev j .a}
  | .stp j => if off j.val then {.lev j.castSucc .b} else {.lev j.succ .a}
  | .pnd _ => ∅

def chainInX (M : ℕ) (off : ℕ → Bool) : CV M → Finset (CV M)
  | .lev j .a =>
      if h : 0 < j.val ∧ off (j.val - 1) = false then
        {.lev j .c, .stp ⟨j.val - 1, by have := j.isLt; omega⟩} else {.lev j .c}
  | .lev j .b => if h : j.val < M ∧ off j.val = true then {.lev j .a, .stp ⟨j.val, h.1⟩} else {.lev j .a}
  | .lev j .c => if h : j.val < M then {.lev j .b, .lev ⟨j.val + 1, by omega⟩ .a} else {.lev j .b}
  | .stp j => {.lev j.castSucc .c}
  | .pnd j => {.lev j.castSucc .b}

lemma chainOut_irrefl (M : ℕ) (off : ℕ → Bool) (x : CV M) : x ∉ chainOut M off x := by
  rcases x with ⟨j, _ | _ | _⟩ | j | j <;> simp only [chainOut] <;> (try split_ifs) <;>
    simp [Fin.ext_iff] <;> omega

lemma card_chainOut (M : ℕ) (off : ℕ → Bool) (x : CV M) : (chainOut M off x).card ≤ 2 := by
  rcases x with ⟨j, _ | _ | _⟩ | j | j <;> simp only [chainOut] <;> (try split_ifs) <;>
    first | exact card_le_two | simp

lemma card_chainInX (M : ℕ) (off : ℕ → Bool) (x : CV M) : (chainInX M off x).card ≤ 2 := by
  rcases x with ⟨j, _ | _ | _⟩ | j | j <;> simp only [chainInX] <;> (try split_ifs) <;>
    first | exact card_le_two | simp

lemma card_chainOut_top (M : ℕ) (off : ℕ → Bool) :
    (chainOut M off (topB M)).card ≤ 1 ∧ (chainOut M off (topC M)).card ≤ 1 := by
  simp [chainOut, topB, topC]

lemma card_chainInX_top (M : ℕ) (off : ℕ → Bool) :
    (chainInX M off (topB M)).card ≤ 1 ∧ (chainInX M off (topC M)).card ≤ 1 := by
  simp [chainInX, topB, topC]

lemma chain_in (M : ℕ) (off : ℕ → Bool) (x y : CV M) (h : y ∈ chainOut M off x) :
    x ∈ chainInX M off y := by
  rcases x with ⟨j, _ | _ | _⟩ | j | j <;> simp only [chainOut] at h
  · split_ifs at h with h1
    · simp only [mem_insert, mem_singleton] at h
      rcases h with rfl | rfl
      · simp only [chainInX]; split_ifs <;> simp
      · have hj : j.val - 1 < M := by have := j.isLt; omega
        simp only [chainInX, hj, dite_true, mem_insert, mem_singleton]
        right; simp [Fin.ext_iff]; omega
    · simp only [mem_singleton] at h; subst h; simp only [chainInX]; split_ifs <;> simp
  · split_ifs at h with h1
    · simp only [mem_insert, mem_singleton] at h
      rcases h with rfl | rfl
      · simp only [chainInX]; split_ifs <;> simp
      · simp [chainInX]
    · simp only [mem_singleton] at h; subst h; simp only [chainInX]; split_ifs <;> simp
  · split_ifs at h with h1
    · simp only [mem_insert, mem_singleton] at h
      rcases h with rfl | rfl
      · simp only [chainInX]; split_ifs <;> simp
      · simp [chainInX]
    · simp only [mem_singleton] at h; subst h; simp only [chainInX]; split_ifs <;> simp
  · split_ifs at h with h1
    · simp only [mem_singleton] at h; subst h; simp [chainInX, h1]
    · simp only [mem_singleton] at h; subst h
      simp [chainInX, h1, Fin.ext_iff]
  · simp at h

/-! ### The vertex type -/

inductive Vx (n k M : ℕ)
  | T : Fin n → Fin (k+1) → R4 → Vx n k M
  | R : Fin k → Fin (n+1) → R4 → Vx n k M
  | N : Fin k → Fin n → Vx n k M
  | C : Fin k → CV M → Vx n k M
  | Lt : Fin k → Fin n → Bool → Vx n k M
  | Ch : Fin k → Fin n → Bool → CV M → Vx n k M
  deriving DecidableEq

abbrev IF (n k : ℕ) := (Fin n × Fin (k+1) × R4) ⊕ (Fin k × Fin (n+1) × R4) ⊕ (Fin k × Fin n)
abbrev BK (n k : ℕ) := Fin k ⊕ (Fin k × Fin n × Bool) ⊕ (Fin k × Fin n × Bool)

def WB (n k M : ℕ) : BK n k → Type
  | Sum.inl _ => CV M
  | Sum.inr (Sum.inl _) => Unit
  | Sum.inr (Sum.inr _) => CV M

instance instFintypeWB (n k M : ℕ) : ∀ b, Fintype (WB n k M b)
  | Sum.inl _ => inferInstanceAs (Fintype (CV M))
  | Sum.inr (Sum.inl _) => inferInstanceAs (Fintype Unit)
  | Sum.inr (Sum.inr _) => inferInstanceAs (Fintype (CV M))

instance instDecEqWB (n k M : ℕ) : ∀ b, DecidableEq (WB n k M b)
  | Sum.inl _ => inferInstanceAs (DecidableEq (CV M))
  | Sum.inr (Sum.inl _) => inferInstanceAs (DecidableEq Unit)
  | Sum.inr (Sum.inr _) => inferInstanceAs (DecidableEq (CV M))

abbrev SV (n k M : ℕ) := IF n k ⊕ (Σ b : BK n k, WB n k M b)

def toSum {n k M : ℕ} : Vx n k M → SV n k M
  | .T i t r => Sum.inl (Sum.inl (i, t, r))
  | .R e t r => Sum.inl (Sum.inr (Sum.inl (e, t, r)))
  | .N e i => Sum.inl (Sum.inr (Sum.inr (e, i)))
  | .C e w => Sum.inr ⟨Sum.inl e, w⟩
  | .Lt e i b => Sum.inr ⟨Sum.inr (Sum.inl (e, i, b)), ()⟩
  | .Ch e i d w => Sum.inr ⟨Sum.inr (Sum.inr (e, i, d)), w⟩

def ofSum {n k M : ℕ} : SV n k M → Vx n k M
  | Sum.inl (Sum.inl (i, t, r)) => .T i t r
  | Sum.inl (Sum.inr (Sum.inl (e, t, r))) => .R e t r
  | Sum.inl (Sum.inr (Sum.inr (e, i))) => .N e i
  | Sum.inr ⟨Sum.inl e, w⟩ => .C e w
  | Sum.inr ⟨Sum.inr (Sum.inl (e, i, b)), _⟩ => .Lt e i b
  | Sum.inr ⟨Sum.inr (Sum.inr (e, i, d)), w⟩ => .Ch e i d w

def vxEquiv (n k M : ℕ) : Vx n k M ≃ SV n k M where
  toFun := toSum
  invFun := ofSum
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with ((⟨i, t, r⟩ | ⟨e, t, r⟩ | ⟨e, i⟩) | ⟨(e | ⟨e, i, b⟩ | ⟨e, i, d⟩), w⟩) <;> rfl

instance (n k M : ℕ) : Fintype (Vx n k M) := Fintype.ofEquiv _ (vxEquiv n k M).symm

/-! ### Edges -/

section graph
variable {n k M : ℕ} (offU offC : ℕ → Bool)

def outN : Vx n k M → Finset (Vx n k M)
  | .T i t .a =>
      if h : 0 < t.val then {.T i t .b, .T i ⟨t.val - 1, by have := t.isLt; omega⟩ .c} else {.T i t .b}
  | .T i t .b => if h : t.val < k then {.T i t .b2, .Lt ⟨t.val, h⟩ i true} else {.T i t .b2}
  | .T i t .b2 => if h : t.val < k then {.T i t .c, .Ch ⟨t.val, h⟩ i false (topB M)} else {.T i t .c}
  | .T i t .c => if h : t.val < k then {.T i t .a, .T i ⟨t.val + 1, by omega⟩ .a} else {.T i t .a}
  | .R e t .a =>
      if h : 0 < t.val then {.R e t .b, .R e ⟨t.val - 1, by have := t.isLt; omega⟩ .c} else {.R e t .b}
  | .R e t .b => if t.val = n then {.R e t .b2, .C e (topB M)} else {.R e t .b2}
  | .R e t .b2 => {.R e t .c}
  | .R e t .c => if h : t.val < n then {.R e t .a, .R e ⟨t.val + 1, by omega⟩ .a} else {.R e t .a}
  | .N e i => {.Ch e i false (topC M), .Lt e i false}
  | .Lt e i true => {.T i e.castSucc .b, .R e i.castSucc .b}
  | .Lt e i false => {.N e i, .R e i.castSucc .b2}
  | .C e w => (chainOut M offC w).image (.C e) ∪ (if w = topB M then {.R e (Fin.last n) .b} else ∅)
  | .Ch e i true w => (univ.filter (fun y => w ∈ chainOut M offU y)).image (.Ch e i true) ∪
      (if w = topB M then {.T i e.castSucc .b2} else if w = topC M then {.N e i} else ∅)
  | .Ch e i false w => (chainOut M offU w).image (.Ch e i false)

def inN : Vx n k M → Finset (Vx n k M)
  | .T i t .a =>
      if h : 0 < t.val then {.T i t .c, .T i ⟨t.val - 1, by have := t.isLt; omega⟩ .c} else {.T i t .c}
  | .T i t .b => if h : t.val < k then {.T i t .a, .Lt ⟨t.val, h⟩ i true} else {.T i t .a}
  | .T i t .b2 => if h : t.val < k then {.T i t .b, .Ch ⟨t.val, h⟩ i true (topB M)} else {.T i t .b}
  | .T i t .c => if h : t.val < k then {.T i t .b2, .T i ⟨t.val + 1, by omega⟩ .a} else {.T i t .b2}
  | .R e t .a =>
      if h : 0 < t.val then {.R e t .c, .R e ⟨t.val - 1, by have := t.isLt; omega⟩ .c} else {.R e t .c}
  | .R e t .b => if h : t.val < n then {.R e t .a, .Lt e ⟨t.val, h⟩ true} else {.R e t .a, .C e (topB M)}
  | .R e t .b2 => if h : t.val < n then {.R e t .b, .Lt e ⟨t.val, h⟩ false} else {.R e t .b}
  | .R e t .c => if h : t.val < n then {.R e t .b2, .R e ⟨t.val + 1, by omega⟩ .a} else {.R e t .b2}
  | .N e i => {.Ch e i true (topC M), .Lt e i false}
  | .Lt e i true => {.T i e.castSucc .b}
  | .Lt e i false => {.N e i}
  | .C e w => (chainInX M offC w).image (.C e) ∪ (if w = topB M then {.R e (Fin.last n) .b} else ∅)
  | .Ch e i true w => (chainOut M offU w).image (.Ch e i true)
  | .Ch e i false w => (chainInX M offU w).image (.Ch e i false) ∪
      (if w = topB M then {.T i e.castSucc .b2} else if w = topC M then {.N e i} else ∅)

lemma topB_ne_topC (M : ℕ) : topB M ≠ topC M := by simp [topB, topC]

lemma card_outN (v : Vx n k M) : (outN offU offC v).card ≤ 2 := by
  rcases v with ⟨i, t, (_ | _ | _ | _)⟩ | ⟨e, t, (_ | _ | _ | _)⟩ | ⟨e, i⟩ | ⟨e, w⟩ | ⟨e, i, (_ | _)⟩ |
    ⟨e, i, (_ | _), w⟩
  any_goals (simp only [outN]; (try split_ifs) <;> first | exact card_le_two | (simp; done))
  · simp only [outN]
    refine le_trans (card_union_le _ _) ?_
    split_ifs with h
    · subst h
      have := (card_chainOut_top M offC).1
      have := card_image_le (s := chainOut M offC (topB M)) (f := Vx.C (n := n) e)
      simp; omega
    · have := card_chainOut M offC w
      have := card_image_le (s := chainOut M offC w) (f := Vx.C (n := n) e)
      simp; omega
  · simp only [outN]
    exact card_image_le.trans (card_chainOut M offU w)
  · simp only [outN]
    refine le_trans (card_union_le _ _) ?_
    have hsub : univ.filter (fun y => w ∈ chainOut M offU y) ⊆ chainInX M offU w := by
      intro y hy; simp only [mem_filter, mem_univ, true_and] at hy; exact chain_in M offU y w hy
    have h1 := (card_image_le (s := univ.filter (fun y => w ∈ chainOut M offU y))
      (f := Vx.Ch (n := n) e i true)).trans (card_le_card hsub)
    split_ifs with h h'
    · subst h; have := (card_chainInX_top M offU).1; simp; omega
    · subst h'; have := (card_chainInX_top M offU).2; simp; omega
    · have := card_chainInX M offU w; simp; omega

lemma card_inN (v : Vx n k M) : (inN offU offC v).card ≤ 2 := by
  rcases v with ⟨i, t, (_ | _ | _ | _)⟩ | ⟨e, t, (_ | _ | _ | _)⟩ | ⟨e, i⟩ | ⟨e, w⟩ | ⟨e, i, (_ | _)⟩ |
    ⟨e, i, (_ | _), w⟩
  any_goals (simp only [inN]; (try split_ifs) <;> first | exact card_le_two | (simp; done))
  · simp only [inN]
    refine le_trans (card_union_le _ _) ?_
    split_ifs with h
    · subst h
      have := (card_chainInX_top M offC).1
      have := card_image_le (s := chainInX M offC (topB M)) (f := Vx.C (n := n) e)
      simp; omega
    · have := card_chainInX M offC w
      have := card_image_le (s := chainInX M offC w) (f := Vx.C (n := n) e)
      simp; omega
  · simp only [inN]
    refine le_trans (card_union_le _ _) ?_
    have h1 := card_image_le (s := chainInX M offU w) (f := Vx.Ch (n := n) e i false)
    split_ifs with h h'
    · subst h; have := (card_chainInX_top M offU).1; simp; omega
    · subst h'; have := (card_chainInX_top M offU).2; simp; omega
    · have := card_chainInX M offU w; simp; omega
  · simp only [inN]
    exact card_image_le.trans (card_chainOut M offU w)

lemma outN_irrefl (v : Vx n k M) : v ∉ outN offU offC v := by
  rcases v with ⟨i, t, (_ | _ | _ | _)⟩ | ⟨e, t, (_ | _ | _ | _)⟩ | ⟨e, i⟩ | ⟨e, w⟩ | ⟨e, i, (_ | _)⟩ |
    ⟨e, i, (_ | _), w⟩
  any_goals (simp only [outN]; (try split_ifs) <;>
    first | (simp [Fin.ext_iff]; done) | (simp [Fin.ext_iff]; omega))
  · simp only [outN, mem_union, mem_image, not_or]
    refine ⟨fun ⟨y, hy, he⟩ => ?_, ?_⟩
    · simp only [Vx.C.injEq, true_and] at he; subst he; exact chainOut_irrefl M offC y hy
    · split_ifs <;> simp
  · simp only [outN, mem_image, not_exists, not_and]
    intro y hy he
    simp only [Vx.Ch.injEq, true_and] at he; subst he; exact chainOut_irrefl M offU y hy
  · simp only [outN, mem_union, mem_image, mem_filter, mem_univ, true_and, not_or]
    refine ⟨fun ⟨y, hy, he⟩ => ?_, ?_⟩
    · simp only [Vx.Ch.injEq, true_and] at he; subst he; exact chainOut_irrefl M offU y hy
    · split_ifs <;> simp

lemma out_in (u v : Vx n k M) (h : v ∈ outN offU offC u) : u ∈ inN offU offC v := by
  rcases u with ⟨i, t, (_ | _ | _ | _)⟩ | ⟨e, t, (_ | _ | _ | _)⟩ | ⟨e, i⟩ | ⟨e, w⟩ | ⟨e, i, (_ | _)⟩ |
    ⟨e, i, (_ | _), w⟩
  all_goals (try have ht := t.isLt)
  all_goals (try have he := e.isLt)
  all_goals (try have hi := i.isLt)
  any_goals (simp only [outN] at h; (try split_ifs at h with h1) <;>
    simp only [mem_insert, mem_singleton] at h <;>
    (first | (rcases h with rfl | rfl) | subst h) <;>
    simp only [inN, Fin.val_mk, Fin.val_castSucc, Fin.val_last] <;> (try split_ifs) <;>
    simp [Fin.ext_iff] <;> omega)
  any_goals (simp only [outN, mem_insert, mem_singleton] at h; rcases h with rfl | rfl <;>
    simp [inN, Fin.ext_iff, topB_ne_topC, (topB_ne_topC M).symm, he, hi])
  · simp only [outN, mem_union, mem_image] at h
    rcases h with ⟨y, hy, rfl⟩ | h
    · simp only [inN, mem_union, mem_image]
      exact Or.inl ⟨w, chain_in M offC w y hy, rfl⟩
    · split_ifs at h with hw
      · subst hw; simp only [mem_singleton] at h; subst h; simp [inN]
      · simp at h
  · simp only [outN, mem_image] at h
    obtain ⟨y, hy, rfl⟩ := h
    simp only [inN, mem_union, mem_image]
    exact Or.inl ⟨w, chain_in M offU w y hy, rfl⟩
  · simp only [outN, mem_union, mem_image, mem_filter, mem_univ, true_and] at h
    rcases h with ⟨y, hy, rfl⟩ | h
    · simp only [inN, mem_image]
      exact ⟨w, hy, rfl⟩
    · split_ifs at h with hw hw'
      · subst hw; simp only [mem_singleton] at h; subst h; simp [inN, Fin.ext_iff]
      · subst hw'; simp only [mem_singleton] at h; subst h; simp [inN]
      · simp at h

end graph

/-! ### Path decomposition -/

section decomp

def PP (M : ℕ) : ℕ := 4 * M + 6
def DD (M : ℕ) : ℕ := 2 * M + 2

def enc (n M : ℕ) (e i s : ℕ) : ℕ := (e * (n+1) + i) * PP M + s

def lvl (n k M : ℕ) (i t : ℕ) : ℕ := if t < k then enc n M t i 0 else enc n M k 0 i

def cLo (M : ℕ) : CV M → ℕ
  | .lev j .a => 2 * (M - j.val)
  | .lev j .b => 2 * (M - j.val) - 1
  | .lev j .c => 2 * (M - j.val) - 1
  | .stp j => 2 * (M - j.val) - 1
  | .pnd j => 2 * (M - j.val)

def cHi (M : ℕ) : CV M → ℕ
  | .lev j .a => 2 * (M - j.val) + 1
  | .lev j .b => 2 * (M - j.val)
  | .lev j .c => 2 * (M - j.val)
  | .stp j => 2 * (M - j.val) - 1
  | .pnd j => 2 * (M - j.val)

lemma cLo_le_cHi (M : ℕ) (w : CV M) : cLo M w ≤ cHi M w := by
  rcases w with ⟨j, _ | _ | _⟩ | j | j <;> simp only [cLo, cHi] <;> omega

lemma cHi_le (M : ℕ) (w : CV M) : cHi M w ≤ 2 * M + 1 := by
  rcases w with ⟨j, _ | _ | _⟩ | j | j <;> simp only [cHi] <;> omega

lemma chain_overlap (M : ℕ) (off : ℕ → Bool) (x y : CV M) (h : y ∈ chainOut M off x) :
    cLo M x ≤ cHi M y ∧ cLo M y ≤ cHi M x := by
  rcases x with ⟨j, _ | _ | _⟩ | j | j
  all_goals (try have hj := j.isLt)
  all_goals simp only [chainOut] at h
  all_goals (try split_ifs at h with h1)
  all_goals simp only [mem_insert, mem_singleton, Finset.notMem_empty] at h
  all_goals (try rcases h with rfl | rfl)
  all_goals (try subst h)
  all_goals simp [cLo, cHi]
  all_goals omega

variable {n k M : ℕ}

def lo : Vx n k M → ℕ
  | .T i t _ => lvl n k M i t
  | .R e t _ => enc n M e t 0
  | .N e i => enc n M e i 1
  | .Lt e i b => enc n M e i (if b then 0 else 1)
  | .C e w => enc n M e n (cLo M w)
  | .Ch e i d w => enc n M e i (2 + (if d then DD M else 0) + cLo M w)

def hi : Vx n k M → ℕ
  | .T i t .c => if t.val < k then lvl n k M i (t.val + 1) else lvl n k M i t
  | .T i t .b2 => if t.val < k then enc n M t i (2 * DD M + 1) else lvl n k M i t
  | .T i t .a => lvl n k M i t
  | .T i t .b => lvl n k M i t
  | .R e t .c => if t.val < n then enc n M e (t.val + 1) 0 else enc n M e t 0
  | .R e t .b2 => if t.val < n then enc n M e t 1 else enc n M e t 0
  | .R e t .a => enc n M e t 0
  | .R e t .b => enc n M e t 0
  | .N e i => enc n M e i (2 * DD M + 1)
  | .Lt e i b => enc n M e i (if b then 0 else 1)
  | .C e w => enc n M e n (cHi M w)
  | .Ch e i d w => enc n M e i (2 + (if d then DD M else 0) + cHi M w)

def Valid (n k M : ℕ) (e i s : ℕ) : Prop := (e < k ∧ i ≤ n ∧ s < PP M) ∨ (e = k ∧ i = 0)

def LexLt (e i s e' i' s' : ℕ) : Prop := e < e' ∨ (e = e' ∧ i < i') ∨ (e = e' ∧ i = i' ∧ s < s')

lemma enc_lt_of {e i s e' i' s' : ℕ} (va : Valid n k M e i s) (vb : Valid n k M e' i' s')
    (h : LexLt e i s e' i' s') : enc n M e i s < enc n M e' i' s' := by
  unfold enc
  unfold Valid at va vb
  unfold LexLt at h
  rcases h with h | ⟨rfl, h⟩ | ⟨rfl, rfl, h⟩
  · have hs : s < PP M := by rcases va with va | va <;> omega
    have hi : i ≤ n := by rcases va with va | va <;> omega
    have h1 : (e * (n+1) + i) * PP M + s < (e * (n+1) + i + 1) * PP M := by
      rw [add_one_mul]; omega
    have h2 : (e * (n+1) + i + 1) * PP M ≤ (e' * (n+1) + i') * PP M := by
      apply Nat.mul_le_mul_right
      have : (e + 1) * (n+1) ≤ e' * (n+1) := Nat.mul_le_mul_right _ h
      rw [add_one_mul] at this
      omega
    omega
  · have hs : s < PP M := by rcases va with va | va <;> rcases vb with vb | vb <;> omega
    have h1 : (e * (n+1) + i) * PP M + s < (e * (n+1) + i + 1) * PP M := by
      rw [add_one_mul]; omega
    have h2 : (e * (n+1) + i + 1) * PP M ≤ (e * (n+1) + i') * PP M :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  · omega

lemma enc_le_iff {e i s e' i' s' : ℕ} (va : Valid n k M e i s) (vb : Valid n k M e' i' s') :
    enc n M e i s ≤ enc n M e' i' s' ↔ ¬ LexLt e' i' s' e i s := by
  constructor
  · intro h h'
    have := enc_lt_of vb va h'
    omega
  · intro h
    by_cases h' : LexLt e i s e' i' s'
    · exact (enc_lt_of va vb h').le
    · have : e = e' ∧ i = i' ∧ s = s' := by unfold LexLt at h h'; omega
      obtain ⟨rfl, rfl, rfl⟩ := this
      exact le_rfl

lemma PP_eq (M : ℕ) : PP M = 2 * DD M + 2 := by unfold PP DD; ring

lemma valid_ph {e i s : ℕ} (he : e < k) (hi : i ≤ n) (hs : s < PP M) : Valid n k M e i s :=
  Or.inl ⟨he, hi, hs⟩

lemma valid_fin (s : ℕ) : Valid n k M k 0 s := Or.inr ⟨rfl, rfl⟩

lemma valid_lvl (i t : ℕ) (hi : i ≤ n) (ht : t ≤ k) :
    (t < k → Valid n k M t i 0) ∧ Valid n k M k 0 i := by
  refine ⟨fun h => valid_ph h hi (by unfold PP; omega), valid_fin i⟩

end decomp

/-! ### Width of the decomposition -/

section width

def oT (n k M : ℕ) (i t : ℕ) (r : R4) : Option (Vx n k M) :=
  if h : i < n ∧ t ≤ k then some (.T ⟨i, h.1⟩ ⟨t, by omega⟩ r) else none
def oR (n k M : ℕ) (e t : ℕ) (r : R4) : Option (Vx n k M) :=
  if h : e < k ∧ t ≤ n then some (.R ⟨e, h.1⟩ ⟨t, by omega⟩ r) else none
def oN (n k M : ℕ) (e i : ℕ) : Option (Vx n k M) :=
  if h : e < k ∧ i < n then some (.N ⟨e, h.1⟩ ⟨i, h.2⟩) else none
def oLt (n k M : ℕ) (e i : ℕ) (b : Bool) : Option (Vx n k M) :=
  if h : e < k ∧ i < n then some (.Lt ⟨e, h.1⟩ ⟨i, h.2⟩ b) else none
def oCh (n k M : ℕ) (e i : ℕ) (d : Bool) (o : Option (CV M)) : Option (Vx n k M) :=
  if h : e < k ∧ i < n then o.map (.Ch ⟨e, h.1⟩ ⟨i, h.2⟩ d) else none
def oC (n k M : ℕ) (e : ℕ) (o : Option (CV M)) : Option (Vx n k M) :=
  if h : e < k then o.map (.C ⟨e, h⟩) else none

def oStp (M d : ℕ) : Option (CV M) :=
  if h : 1 ≤ d ∧ d ≤ M then some (.stp ⟨M - d, by omega⟩) else none
def oPnd (M d : ℕ) : Option (CV M) :=
  if h : 1 ≤ d ∧ d ≤ M then some (.pnd ⟨M - d, by omega⟩) else none

def win (M τ : ℕ) : List (Option (CV M)) :=
  [some (.lev ⟨M - τ / 2, by omega⟩ .a), some (.lev ⟨M - (τ + 1) / 2, by omega⟩ .b),
   some (.lev ⟨M - (τ + 1) / 2, by omega⟩ .c),
   if τ % 2 = 0 then oPnd M (τ / 2) else oStp M ((τ + 1) / 2)]

lemma win_mem (M : ℕ) (w : CV M) (τ : ℕ) (h1 : cLo M w ≤ τ) (h2 : τ ≤ cHi M w) :
    some w ∈ win M τ := by
  rcases w with ⟨⟨j, hj⟩, _ | _ | _⟩ | ⟨j, hj⟩ | ⟨j, hj⟩ <;> simp only [cLo, cHi] at h1 h2
  · simp only [win, List.mem_cons]
    left; simp only [Option.some.injEq, CV.lev.injEq, and_true, Fin.mk.injEq]; omega
  · simp only [win, List.mem_cons]
    right; left; simp only [Option.some.injEq, CV.lev.injEq, and_true, Fin.mk.injEq]; omega
  · simp only [win, List.mem_cons]
    right; right; left; simp only [Option.some.injEq, CV.lev.injEq, and_true, Fin.mk.injEq]; omega
  · simp only [win, List.mem_cons]
    right; right; right; left
    rw [if_neg (by omega), oStp, dif_pos (by omega)]
    simp only [Option.some.injEq, CV.stp.injEq, Fin.mk.injEq]; omega
  · simp only [win, List.mem_cons]
    right; right; right; left
    rw [if_pos (by omega), oPnd, dif_pos (by omega)]
    simp only [Option.some.injEq, CV.pnd.injEq, Fin.mk.injEq]; omega

def localL (n k M : ℕ) (e i s : ℕ) : List (Option (Vx n k M)) :=
  if e < k ∧ i < n then
    if s = 0 then [oT n k M i e .a, oT n k M i e .b, oT n k M i e .b2, oT n k M i e .c,
      oR n k M e (i-1) .c, oR n k M e i .a, oR n k M e i .b, oR n k M e i .b2, oR n k M e i .c,
      oLt n k M e i true]
    else if s = 1 then [oT n k M i e .b2, oT n k M i e .c, oR n k M e i .b2, oR n k M e i .c,
      oN n k M e i, oLt n k M e i false]
    else [oT n k M i e .b2, oT n k M i e .c, oR n k M e i .c, oN n k M e i] ++
      (if s < 2 + DD M then (win M (s - 2)).map (oCh n k M e i false)
       else (win M (s - 2 - DD M)).map (oCh n k M e i true))
  else if e < k then
    [oR n k M e (n-1) .c, oR n k M e n .a, oR n k M e n .b, oR n k M e n .b2, oR n k M e n .c] ++
      (win M s).map (oC n k M e)
  else [oT n k M s k .a, oT n k M s k .b, oT n k M s k .b2, oT n k M s k .c]

lemma length_localL (n k M e i s : ℕ) : (localL n k M e i s).length ≤ 11 := by
  unfold localL; split_ifs <;> simp [win]

def ofList {α : Type*} [DecidableEq α] (l : List (Option α)) : Finset α := (l.filterMap id).toFinset

lemma card_ofList {α : Type*} [DecidableEq α] (l : List (Option α)) : (ofList l).card ≤ l.length :=
  (List.toFinset_card_le _).trans (List.length_filterMap_le _ _)

lemma mem_ofList {α : Type*} [DecidableEq α] (l : List (Option α)) (a : α) :
    a ∈ ofList l ↔ some a ∈ l := by
  simp [ofList, List.mem_filterMap]

def carried (n k M : ℕ) (e i : ℕ) : Finset (Vx n k M) :=
  univ.image (fun i' : Fin n => Vx.T i' ⟨min (if i'.val < i then e else e - 1) k, by omega⟩ .c)

def bag (n k M e i s : ℕ) : Finset (Vx n k M) := carried n k M e i ∪ ofList (localL n k M e i s)

lemma card_bag (n k M e i s : ℕ) : (bag n k M e i s).card ≤ n + 11 := by
  unfold bag
  refine le_trans (card_union_le _ _) ?_
  have h1 : (carried n k M e i).card ≤ n := card_image_le.trans (by simp)
  have h2 := (card_ofList (localL n k M e i s)).trans (length_localL n k M e i s)
  omega

lemma mem_bag_local {n k M e i s : ℕ} {v : Vx n k M} (h : some v ∈ localL n k M e i s) :
    v ∈ bag n k M e i s := mem_union_right _ ((mem_ofList _ _).2 h)

lemma enc_lt_P {n M e i s : ℕ} (h : s < PP M) : enc n M e i s < enc n M e i (PP M) := by
  unfold enc; omega

lemma alive_sub {n k M e i s : ℕ} (hv : Valid n k M e i s) (v : Vx n k M)
    (h1 : lo v ≤ enc n M e i s) (h2 : enc n M e i s ≤ hi v) : v ∈ bag n k M e i s := by
  have hP : PP M = 2 * DD M + 2 := PP_eq M
  have hD : DD M = 2 * M + 2 := rfl
  have hv' := hv
  unfold Valid at hv'
  rcases v with ⟨⟨i0, hi0⟩, ⟨t0, ht0⟩, r⟩ | ⟨⟨e0, he0⟩, ⟨t0, ht0⟩, r⟩ | ⟨⟨e0, he0⟩, ⟨i0, hi0⟩⟩ |
    ⟨⟨e0, he0⟩, w⟩ | ⟨⟨e0, he0⟩, ⟨i0, hi0⟩, b⟩ | ⟨⟨e0, he0⟩, ⟨i0, hi0⟩, d, w⟩
  · -- track vertex
    by_cases ht : t0 < k
    · have va : Valid n k M t0 i0 0 := valid_ph ht (by omega) (by omega)
      have hlo : lo (Vx.T (n := n) (k := k) (M := M) ⟨i0, hi0⟩ ⟨t0, ht0⟩ r) = enc n M t0 i0 0 := by
        simp [lo, lvl, ht]
      rw [hlo, enc_le_iff va hv] at h1
      unfold LexLt at h1
      rcases r with _ | _ | _ | _
      · simp only [hi, lvl, if_pos ht] at h2
        rw [enc_le_iff hv va] at h2; unfold LexLt at h2
        obtain ⟨rfl, rfl, rfl⟩ : e = t0 ∧ i = i0 ∧ s = 0 := by omega
        apply mem_bag_local
        rw [localL, if_pos ⟨ht, hi0⟩, if_pos rfl]
        simp [oT, hi0, ht.le]
      · simp only [hi, lvl, if_pos ht] at h2
        rw [enc_le_iff hv va] at h2; unfold LexLt at h2
        obtain ⟨rfl, rfl, rfl⟩ : e = t0 ∧ i = i0 ∧ s = 0 := by omega
        apply mem_bag_local
        rw [localL, if_pos ⟨ht, hi0⟩, if_pos rfl]
        simp [oT, hi0, ht.le]
      · simp only [hi, if_pos ht] at h2
        rw [enc_le_iff hv (valid_ph ht (by omega) (by omega))] at h2; unfold LexLt at h2
        obtain ⟨rfl, rfl⟩ : e = t0 ∧ i = i0 := by omega
        apply mem_bag_local
        rw [localL, if_pos ⟨ht, hi0⟩]
        rcases (show s = 0 ∨ s = 1 ∨ 2 ≤ s by omega) with rfl | rfl | hs
        · rw [if_pos rfl]; simp [oT, hi0, ht.le]
        · rw [if_neg (by omega), if_pos rfl]; simp [oT, hi0, ht.le]
        · rw [if_neg (by omega), if_neg (by omega)]; simp [oT, hi0, ht.le]
      · simp only [hi, if_pos ht, lvl] at h2
        by_cases hloc : e = t0 ∧ i = i0
        · obtain ⟨rfl, rfl⟩ := hloc
          apply mem_bag_local
          rw [localL, if_pos ⟨ht, hi0⟩]
          rcases (show s = 0 ∨ s = 1 ∨ 2 ≤ s by omega) with rfl | rfl | hs
          · rw [if_pos rfl]; simp [oT, hi0, ht.le]
          · rw [if_neg (by omega), if_pos rfl]; simp [oT, hi0, ht.le]
          · rw [if_neg (by omega), if_neg (by omega)]; simp [oT, hi0, ht.le]
        · apply mem_union_left
          simp only [carried, mem_image, mem_univ, true_and]
          refine ⟨⟨i0, hi0⟩, ?_⟩
          simp only [Vx.T.injEq, Fin.mk.injEq, true_and, and_true]
          split_ifs at h2 with ht1
          · rw [enc_le_iff hv (valid_ph ht1 (by omega) (by omega))] at h2; unfold LexLt at h2
            split_ifs <;> omega
          · rw [enc_le_iff hv (valid_fin i0)] at h2; unfold LexLt at h2
            split_ifs <;> omega
    · have ht' : t0 = k := by omega
      subst ht'
      have hlo : lo (Vx.T (n := n) (k := t0) (M := M) ⟨i0, hi0⟩ ⟨t0, ht0⟩ r) = enc n M t0 0 i0 := by
        simp [lo, lvl]
      have hhi : hi (Vx.T (n := n) (k := t0) (M := M) ⟨i0, hi0⟩ ⟨t0, ht0⟩ r) = enc n M t0 0 i0 := by
        rcases r with _ | _ | _ | _ <;> simp [hi, lvl]
      rw [hlo, enc_le_iff (valid_fin i0) hv] at h1
      rw [hhi, enc_le_iff hv (valid_fin i0)] at h2
      unfold LexLt at h1 h2
      obtain ⟨rfl, rfl, rfl⟩ : e = t0 ∧ i = 0 ∧ s = i0 := by omega
      apply mem_bag_local
      rw [localL, if_neg (by omega), if_neg (by omega)]
      rcases r with _ | _ | _ | _ <;> simp [oT, hi0]
  · -- ring vertex
    have va : Valid n k M e0 t0 0 := valid_ph he0 (by omega) (by omega)
    have hlo : lo (Vx.R (n := n) (k := k) (M := M) ⟨e0, he0⟩ ⟨t0, ht0⟩ r) = enc n M e0 t0 0 := by
      simp [lo]
    rw [hlo, enc_le_iff va hv] at h1
    unfold LexLt at h1
    by_cases htn : t0 < n
    · rcases r with _ | _ | _ | _
      · simp only [hi] at h2
        rw [enc_le_iff hv va] at h2; unfold LexLt at h2
        obtain ⟨rfl, rfl, rfl⟩ : e = e0 ∧ i = t0 ∧ s = 0 := by omega
        apply mem_bag_local
        rw [localL, if_pos ⟨he0, htn⟩, if_pos rfl]
        simp [oR, he0, ht0, Nat.le_of_lt_succ ht0]
      · simp only [hi] at h2
        rw [enc_le_iff hv va] at h2; unfold LexLt at h2
        obtain ⟨rfl, rfl, rfl⟩ : e = e0 ∧ i = t0 ∧ s = 0 := by omega
        apply mem_bag_local
        rw [localL, if_pos ⟨he0, htn⟩, if_pos rfl]
        simp [oR, he0, ht0, Nat.le_of_lt_succ ht0]
      · simp only [hi, if_pos htn] at h2
        rw [enc_le_iff hv (valid_ph he0 (by omega) (by omega))] at h2; unfold LexLt at h2
        obtain ⟨rfl, rfl⟩ : e = e0 ∧ i = t0 := by omega
        apply mem_bag_local
        rw [localL, if_pos ⟨he0, htn⟩]
        rcases (show s = 0 ∨ s = 1 by omega) with rfl | rfl
        · rw [if_pos rfl]; simp [oR, he0, ht0, Nat.le_of_lt_succ ht0]
        · rw [if_neg (by omega), if_pos rfl]; simp [oR, he0, ht0, Nat.le_of_lt_succ ht0]
      · simp only [hi, if_pos htn] at h2
        rw [enc_le_iff hv (valid_ph he0 (by omega) (by omega))] at h2; unfold LexLt at h2
        by_cases hloc : i = t0
        · obtain ⟨rfl, rfl⟩ : e = e0 ∧ i = t0 := by omega
          apply mem_bag_local
          rw [localL, if_pos ⟨he0, htn⟩]
          rcases (show s = 0 ∨ s = 1 ∨ 2 ≤ s by omega) with rfl | rfl | hs
          · rw [if_pos rfl]; simp [oR, he0, ht0, Nat.le_of_lt_succ ht0]
          · rw [if_neg (by omega), if_pos rfl]; simp [oR, he0, ht0, Nat.le_of_lt_succ ht0]
          · rw [if_neg (by omega), if_neg (by omega)]; simp [oR, he0, ht0, Nat.le_of_lt_succ ht0]
        · obtain ⟨rfl, rfl, rfl⟩ : e = e0 ∧ i = t0 + 1 ∧ s = 0 := by omega
          apply mem_bag_local
          by_cases hn1 : t0 + 1 < n
          · rw [localL, if_pos ⟨he0, hn1⟩, if_pos rfl]
            simp [oR, he0, ht0, Nat.le_of_lt_succ ht0]
          · rw [localL, if_neg (by omega), if_pos he0]
            have : n - 1 = t0 := by omega
            simp [oR, he0, ht0, this, Nat.le_of_lt_succ ht0]
    · have htn' : t0 = n := by omega
      subst htn'
      have hhi : hi (Vx.R (n := t0) (k := k) (M := M) ⟨e0, he0⟩ ⟨t0, ht0⟩ r) = enc t0 M e0 t0 0 := by
        rcases r with _ | _ | _ | _ <;> simp [hi]
      rw [hhi, enc_le_iff hv va] at h2; unfold LexLt at h2
      obtain ⟨rfl, rfl, rfl⟩ : e = e0 ∧ i = t0 ∧ s = 0 := by omega
      apply mem_bag_local
      rw [localL, if_neg (by omega), if_pos he0]
      rcases r with _ | _ | _ | _ <;> simp [oR, he0]
  · -- negation vertex
    simp only [lo, hi] at h1 h2
    rw [enc_le_iff (valid_ph he0 (by omega) (by omega)) hv] at h1
    rw [enc_le_iff hv (valid_ph he0 (by omega) (by omega))] at h2
    unfold LexLt at h1 h2
    obtain ⟨rfl, rfl⟩ : e = e0 ∧ i = i0 := by omega
    apply mem_bag_local
    rw [localL, if_pos ⟨he0, hi0⟩]
    rcases (show s = 1 ∨ 2 ≤ s by omega) with rfl | hs
    · rw [if_neg (by omega), if_pos rfl]; simp [oN, he0, hi0]
    · rw [if_neg (by omega), if_neg (by omega)]; simp [oN, he0, hi0]
  · -- counter chain
    simp only [lo, hi] at h1 h2
    have h3 := cHi_le M w
    have h4 := cLo_le_cHi M w
    rw [enc_le_iff (valid_ph he0 le_rfl (by omega)) hv] at h1
    rw [enc_le_iff hv (valid_ph he0 le_rfl (by omega))] at h2
    unfold LexLt at h1 h2
    obtain ⟨rfl, rfl⟩ : e = e0 ∧ i = n := by omega
    apply mem_bag_local
    rw [localL, if_neg (by omega), if_pos he0]
    simp only [List.mem_append, List.mem_map]
    right
    exact ⟨some w, win_mem M w s (by omega) (by omega), by simp [oC, he0]⟩
  · -- literal vertex
    simp only [lo, hi] at h1 h2
    rw [enc_le_iff (valid_ph he0 (by omega) (by split_ifs <;> omega)) hv] at h1
    rw [enc_le_iff hv (valid_ph he0 (by omega) (by split_ifs <;> omega))] at h2
    unfold LexLt at h1 h2
    apply mem_bag_local
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte] at h1 h2
      obtain ⟨rfl, rfl, rfl⟩ : e = e0 ∧ i = i0 ∧ s = 1 := by omega
      rw [localL, if_pos ⟨he0, hi0⟩, if_neg (by omega), if_pos rfl]
      simp [oLt, he0, hi0]
    · simp only [↓reduceIte] at h1 h2
      obtain ⟨rfl, rfl, rfl⟩ : e = e0 ∧ i = i0 ∧ s = 0 := by omega
      rw [localL, if_pos ⟨he0, hi0⟩, if_pos rfl]
      simp [oLt, he0, hi0]
  · -- negation chains
    simp only [lo, hi] at h1 h2
    have h3 := cHi_le M w
    have h4 := cLo_le_cHi M w
    rw [enc_le_iff (valid_ph he0 (by omega) (by split_ifs <;> omega)) hv] at h1
    rw [enc_le_iff hv (valid_ph he0 (by omega) (by split_ifs <;> omega))] at h2
    unfold LexLt at h1 h2
    apply mem_bag_local
    cases d
    · simp only [Bool.false_eq_true, ↓reduceIte, add_zero] at h1 h2
      obtain ⟨rfl, rfl⟩ : e = e0 ∧ i = i0 := by omega
      rw [localL, if_pos ⟨he0, hi0⟩, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      simp only [List.mem_append, List.mem_map]
      right
      exact ⟨some w, win_mem M w (s - 2) (by omega) (by omega), by simp [oCh, he0, hi0]⟩
    · simp only [↓reduceIte] at h1 h2
      obtain ⟨rfl, rfl⟩ : e = e0 ∧ i = i0 := by omega
      rw [localL, if_pos ⟨he0, hi0⟩, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      simp only [List.mem_append, List.mem_map]
      right
      exact ⟨some w, win_mem M w (s - 2 - DD M) (by omega) (by omega), by simp [oCh, he0, hi0]⟩

lemma hi_lt {n k M : ℕ} (v : Vx n k M) : hi v < enc n M k 0 n := by
  have hP : PP M = 2 * DD M + 2 := PP_eq M
  have hD : DD M = 2 * M + 2 := rfl
  have key : ∀ e i s, e < k → i ≤ n → s < PP M → enc n M e i s < enc n M k 0 n :=
    fun e i s he hi hs => enc_lt_of (valid_ph he hi hs) (valid_fin n) (Or.inl he)
  rcases v with ⟨⟨i0, hi0⟩, ⟨t0, ht0⟩, r⟩ | ⟨⟨e0, he0⟩, ⟨t0, ht0⟩, r⟩ | ⟨⟨e0, he0⟩, ⟨i0, hi0⟩⟩ |
    ⟨⟨e0, he0⟩, w⟩ | ⟨⟨e0, he0⟩, ⟨i0, hi0⟩, b⟩ | ⟨⟨e0, he0⟩, ⟨i0, hi0⟩, d, w⟩
  · have hfin : ∀ j, j < n → enc n M k 0 j < enc n M k 0 n := fun j hj => by unfold enc; omega
    rcases r with _ | _ | _ | _ <;> simp only [hi, lvl] <;> split_ifs <;>
      first | exact hfin _ hi0 | exact key _ _ _ (by omega) (by omega) (by omega)
  · rcases r with _ | _ | _ | _ <;> simp only [hi] <;> (try split_ifs) <;>
      exact key _ _ _ he0 (by omega) (by omega)
  · simp only [hi]; exact key _ _ _ he0 (by omega) (by omega)
  · simp only [hi]; have := cHi_le M w; exact key _ _ _ he0 le_rfl (by omega)
  · simp only [hi]; exact key _ _ _ he0 (by omega) (by split_ifs <;> omega)
  · simp only [hi]; have := cHi_le M w; exact key _ _ _ he0 (by omega) (by split_ifs <;> omega)

lemma width {n k M : ℕ} (t : ℕ) :
    (univ.filter (fun v : Vx n k M => lo v ≤ t ∧ t ≤ hi v)).card ≤ n + 11 := by
  have hP0 : 0 < PP M := by unfold PP; omega
  by_cases hl : enc n M k 0 n ≤ t
  · have : univ.filter (fun v : Vx n k M => lo v ≤ t ∧ t ≤ hi v) = ∅ := by
      apply filter_false_of_mem
      intro v _ hv
      have := hi_lt v
      omega
    rw [this]; simp
  by_cases ht : t < enc n M k 0 0
  · have hq1 := Nat.div_add_mod t (PP M)
    have hq2 := Nat.div_add_mod (t / PP M) (n + 1)
    have hs : t % PP M < PP M := Nat.mod_lt _ hP0
    have hi' : t / PP M % (n+1) < n + 1 := Nat.mod_lt _ (by omega)
    have hφ : t / PP M < k * (n + 1) := by
      rw [Nat.div_lt_iff_lt_mul hP0]; unfold enc at ht; simpa using ht
    have he : t / PP M / (n+1) < k := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; exact hφ
    have hv : Valid n k M (t / PP M / (n+1)) (t / PP M % (n+1)) (t % PP M) :=
      valid_ph he (by omega) hs
    have htt : t = enc n M (t / PP M / (n+1)) (t / PP M % (n+1)) (t % PP M) := by
      unfold enc
      have : t / PP M / (n + 1) * (n + 1) + t / PP M % (n + 1) = t / PP M := by
        rw [mul_comm]; exact hq2
      rw [this, mul_comm]; omega
    have hsub : univ.filter (fun v : Vx n k M => lo v ≤ t ∧ t ≤ hi v) ⊆
        bag n k M (t / PP M / (n+1)) (t / PP M % (n+1)) (t % PP M) := by
      intro v hv'
      simp only [mem_filter, mem_univ, true_and] at hv'
      rw [htt] at hv'
      exact alive_sub hv v hv'.1 hv'.2
    exact le_trans (card_le_card hsub) (card_bag n k M _ _ _)
  · have htt : t = enc n M k 0 (t - enc n M k 0 0) := by unfold enc at *; omega
    have hsub : univ.filter (fun v : Vx n k M => lo v ≤ t ∧ t ≤ hi v) ⊆
        bag n k M k 0 (t - enc n M k 0 0) := by
      intro v hv'
      simp only [mem_filter, mem_univ, true_and] at hv'
      rw [htt] at hv'
      exact alive_sub (valid_fin _) v hv'.1 hv'.2
    exact le_trans (card_le_card hsub) (card_bag n k M _ _ _)

end width

/-! ### Edges are covered -/

lemma enc_le_of_lex {n k M e i s e' i' s' : ℕ} (va : Valid n k M e i s) (vb : Valid n k M e' i' s')
    (h : ¬ LexLt e' i' s' e i s) : enc n M e i s ≤ enc n M e' i' s' := (enc_le_iff va vb).2 h

lemma edge_ok {n k M : ℕ} (offU offC : ℕ → Bool) (u v : Vx n k M) (h : v ∈ outN offU offC u) :
    lo u ≤ hi v ∧ lo v ≤ hi u := by
  have hP : PP M = 2 * DD M + 2 := PP_eq M
  have hD : DD M = 2 * M + 2 := rfl
  rcases u with ⟨i, t, (_ | _ | _ | _)⟩ | ⟨e, t, (_ | _ | _ | _)⟩ | ⟨e, i⟩ | ⟨e, w⟩ | ⟨e, i, (_ | _)⟩ |
    ⟨e, i, (_ | _), w⟩
  all_goals (try have ht := t.isLt)
  all_goals (try have he := e.isLt)
  all_goals (try have hii := i.isLt)
  all_goals try (simp only [outN] at h; (try split_ifs at h with h1) <;>
    simp only [mem_insert, mem_singleton] at h <;>
    (first | (rcases h with rfl | rfl) | subst h) <;>
    simp [lo, hi, lvl, cLo, cHi, topB, topC] <;> (try split_ifs) <;> (try refine ⟨?_, ?_⟩) <;> (first | (unfold enc; omega) | (apply enc_le_of_lex (k := k) <;> (try unfold Valid) <;> (try unfold LexLt) <;> (try unfold PP) <;> omega)))
  · simp only [outN, mem_union, mem_image] at h
    rcases h with ⟨y, hy, rfl⟩ | h
    · have := chain_overlap M offC w y hy
      simp only [lo, hi]; constructor <;> (first | (unfold enc; omega) | (apply enc_le_of_lex (k := k) <;> (try unfold Valid) <;> (try unfold LexLt) <;> (try unfold PP) <;> omega))
    · split_ifs at h with hw
      · subst hw; simp only [mem_singleton] at h; subst h
        simp [lo, hi, cLo, cHi, topB]
      · simp at h
  · simp only [outN, mem_image] at h
    obtain ⟨y, hy, rfl⟩ := h
    have := chain_overlap M offU w y hy
    simp only [lo, hi]; constructor <;> (first | (unfold enc; omega) | (apply enc_le_of_lex (k := k) <;> (try unfold Valid) <;> (try unfold LexLt) <;> (try unfold PP) <;> omega))
  · simp only [outN, mem_union, mem_image, mem_filter, mem_univ, true_and] at h
    rcases h with ⟨y, hy, rfl⟩ | h
    · have := chain_overlap M offU y w hy
      simp only [lo, hi]; constructor <;> (first | (unfold enc; omega) | (apply enc_le_of_lex (k := k) <;> (try unfold Valid) <;> (try unfold LexLt) <;> (try unfold PP) <;> omega))
    · split_ifs at h with hw hw'
      · subst hw; simp only [mem_singleton] at h; subst h
        simp [lo, hi, lvl, cLo, cHi, topB, he]; constructor <;> (first | (unfold enc; omega) | (apply enc_le_of_lex (k := k) <;> (try unfold Valid) <;> (try unfold LexLt) <;> (try unfold PP) <;> omega))
      · subst hw'; simp only [mem_singleton] at h; subst h
        simp [lo, hi, cLo, cHi, topC]; constructor <;> (first | (unfold enc; omega) | (apply enc_le_of_lex (k := k) <;> (try unfold Valid) <;> (try unfold LexLt) <;> (try unfold PP) <;> omega))
      · simp at h

lemma lo_le_hi {n k M : ℕ} (v : Vx n k M) : lo v ≤ hi v := by
  have hP : PP M = 2 * DD M + 2 := PP_eq M
  have hD : DD M = 2 * M + 2 := rfl
  rcases v with ⟨⟨i0, hi0⟩, ⟨t0, ht0⟩, (_ | _ | _ | _)⟩ | ⟨⟨e0, he0⟩, ⟨t0, ht0⟩, (_ | _ | _ | _)⟩ |
    ⟨⟨e0, he0⟩, ⟨i0, hi0⟩⟩ | ⟨⟨e0, he0⟩, w⟩ | ⟨⟨e0, he0⟩, ⟨i0, hi0⟩, b⟩ | ⟨⟨e0, he0⟩, ⟨i0, hi0⟩, d, w⟩
  all_goals (try have := cLo_le_cHi M w)
  all_goals (try have := cHi_le M w)
  all_goals simp only [lo, hi, lvl]
  all_goals (try split_ifs)
  all_goals (first | (unfold enc; omega) | (apply enc_le_of_lex (k := k) <;> (try unfold Valid) <;> (try unfold LexLt) <;> (try unfold PP) <;> omega))

/-! ### Counting the covers -/

section count

lemma bool_eq_of_imp {a b : Bool} (h1 : a = true → b = true) (h2 : b = true → a = true) : a = b := by
  cases a <;> cases b <;> simp_all

def cAct {M : ℕ} (pres : ℕ → Bool) : CV M → Bool
  | .stp j => pres j.val
  | .lev _ _ => true
  | .pnd _ => true

def cClosed {M : ℕ} (off pres : ℕ → Bool) (w : CV M → Bool) : Prop :=
  ∀ x, (cAct pres x = false → w x = true) ∧
    (cAct pres x = true → w x = true → ∀ y ∈ chainOut M off x, w y = true)

def rClosed {M : ℕ} (off : ℕ → Bool) (w : CV M → Bool) : Prop :=
  ∀ x y, y ∈ chainOut M off x → w y = true → w x = true

lemma mem_out_ab {M : ℕ} (off : ℕ → Bool) (j : Fin (M+1)) :
    CV.lev j .b ∈ chainOut M off (.lev j .a) := by
  simp only [chainOut]; split_ifs <;> simp
lemma mem_out_bc {M : ℕ} (off : ℕ → Bool) (j : Fin (M+1)) :
    CV.lev j .c ∈ chainOut M off (.lev j .b) := by
  simp only [chainOut]; split_ifs <;> simp
lemma mem_out_ca {M : ℕ} (off : ℕ → Bool) (j : Fin (M+1)) :
    CV.lev j .a ∈ chainOut M off (.lev j .c) := by
  simp only [chainOut]; split_ifs <;> simp
lemma mem_out_link {M : ℕ} (off : ℕ → Bool) (j : Fin M) :
    CV.lev j.castSucc .c ∈ chainOut M off (.lev j.succ .a) := by
  simp only [chainOut, Fin.val_succ]; rw [dif_pos (by omega)]; simp [Fin.ext_iff]
lemma mem_out_pnd {M : ℕ} (off : ℕ → Bool) (j : Fin M) :
    CV.pnd j ∈ chainOut M off (.lev j.castSucc .b) := by
  simp only [chainOut, Fin.val_castSucc]; rw [dif_pos j.isLt]; simp
lemma mem_out_stp {M : ℕ} (off : ℕ → Bool) (j : Fin M) :
    CV.stp j ∈ chainOut M off (.lev j.castSucc .c) := by
  simp only [chainOut, Fin.val_castSucc]; rw [dif_pos j.isLt]; simp

lemma out_lev_a {M : ℕ} {off : ℕ → Bool} {j : Fin (M+1)} {y : CV M}
    (h : y ∈ chainOut M off (.lev j .a)) :
    y = .lev j .b ∨ ∃ j' : Fin M, j = j'.succ ∧ y = .lev j'.castSucc .c := by
  simp only [chainOut] at h
  split_ifs at h with h1
  · simp only [mem_insert, mem_singleton] at h
    rcases h with rfl | rfl
    · left; rfl
    · right; refine ⟨⟨j.val - 1, by have := j.isLt; omega⟩, Fin.ext (by simp; omega), rfl⟩
  · simp only [mem_singleton] at h; left; exact h

lemma out_lev_b {M : ℕ} {off : ℕ → Bool} {j : Fin (M+1)} {y : CV M}
    (h : y ∈ chainOut M off (.lev j .b)) :
    y = .lev j .c ∨ ∃ j' : Fin M, j = j'.castSucc ∧ y = .pnd j' := by
  simp only [chainOut] at h
  split_ifs at h with h1
  · simp only [mem_insert, mem_singleton] at h
    rcases h with rfl | rfl
    · left; rfl
    · right; exact ⟨⟨j.val, h1⟩, rfl, rfl⟩
  · simp only [mem_singleton] at h; left; exact h

lemma out_lev_c {M : ℕ} {off : ℕ → Bool} {j : Fin (M+1)} {y : CV M}
    (h : y ∈ chainOut M off (.lev j .c)) :
    y = .lev j .a ∨ ∃ j' : Fin M, j = j'.castSucc ∧ y = .stp j' := by
  simp only [chainOut] at h
  split_ifs at h with h1
  · simp only [mem_insert, mem_singleton] at h
    rcases h with rfl | rfl
    · left; rfl
    · right; exact ⟨⟨j.val, h1⟩, rfl, rfl⟩
  · simp only [mem_singleton] at h; left; exact h

lemma cv_symm_inl {M : ℕ} (j : Fin (M+1)) (r : Fin 3) :
    (cvEquiv M).symm (Sum.inl (j, r)) = .lev j (R3.ofFin r) := rfl
lemma cv_symm_stp {M : ℕ} (j : Fin M) (u : Unit) :
    (cvEquiv M).symm (Sum.inr ⟨Sum.inl j, u⟩) = .stp j := rfl
lemma cv_symm_pnd {M : ℕ} (j : Fin M) (u : Unit) :
    (cvEquiv M).symm (Sum.inr ⟨Sum.inr j, u⟩) = .pnd j := rfl
lemma ofFin0 : R3.ofFin 0 = .a := rfl
lemma ofFin1 : R3.ofFin 1 = .b := rfl
lemma ofFin2 : R3.ofFin 2 = .c := rfl

lemma cClosed_iff {M : ℕ} (off pres : ℕ → Bool) (τ : Bool) (w : CV M → Bool) :
    (cClosed off pres w ∧ w (topB M) = τ) ↔
    (chainPI M τ (fun i => w ((cvEquiv M).symm (Sum.inl i))) ∧
      ∀ b, chainPB M pres off b (fun i => w ((cvEquiv M).symm (Sum.inl i)))
        (fun u => w ((cvEquiv M).symm (Sum.inr ⟨b, u⟩)))) := by
  simp only [chainPI, cv_symm_inl, ofFin0, ofFin1, ofFin2, topB]
  constructor
  · rintro ⟨hc, rfl⟩
    refine ⟨⟨fun j => ⟨fun h => (hc _).2 rfl h _ (mem_out_ab off j),
        fun h => (hc _).2 rfl h _ (mem_out_bc off j), fun h => (hc _).2 rfl h _ (mem_out_ca off j)⟩,
      fun j h => (hc _).2 rfl h _ (mem_out_link off j), rfl⟩, fun b => ?_⟩
    rcases b with j | j
    · simp only [chainPB, cv_symm_stp, cv_symm_inl, ofFin0, ofFin1, ofFin2, stopOK]
      cases hp : pres j.val
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact (hc (.stp j)).1 (by simp [cAct, hp])
      · simp only [↓reduceIte]
        refine ⟨fun h => (hc _).2 rfl h _ (mem_out_stp off j), fun h => ?_⟩
        have := (hc (.stp j)).2 (by simp [cAct, hp]) h
        cases ho : off j.val
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact this _ (by simp [chainOut, ho])
        · simp only [↓reduceIte]; exact this _ (by simp [chainOut, ho])
    · simp only [chainPB, cv_symm_pnd, cv_symm_inl, ofFin1]
      exact fun h => (hc _).2 rfl h _ (mem_out_pnd off j)
  · rintro ⟨⟨hlev, hlink, htop⟩, hb⟩
    refine ⟨fun x => ?_, htop⟩
    rcases x with ⟨j, _ | _ | _⟩ | j | j
    · refine ⟨fun h => by simp [cAct] at h, fun _ hw y hy => ?_⟩
      rcases out_lev_a hy with rfl | ⟨j', rfl, rfl⟩
      · exact (hlev j).1 hw
      · exact hlink j' hw
    · refine ⟨fun h => by simp [cAct] at h, fun _ hw y hy => ?_⟩
      rcases out_lev_b hy with rfl | ⟨j', rfl, rfl⟩
      · exact (hlev j).2.1 hw
      · have := hb (Sum.inr j')
        simp only [chainPB, cv_symm_pnd, cv_symm_inl, ofFin1] at this; exact this hw
    · refine ⟨fun h => by simp [cAct] at h, fun _ hw y hy => ?_⟩
      rcases out_lev_c hy with rfl | ⟨j', rfl, rfl⟩
      · exact (hlev j).2.2 hw
      · have := hb (Sum.inl j')
        simp only [chainPB, cv_symm_stp, cv_symm_inl, ofFin0, ofFin1, ofFin2, stopOK] at this
        split_ifs at this <;> first | exact this.1 hw | exact this
    · have := hb (Sum.inl j)
      simp only [chainPB, cv_symm_stp, cv_symm_inl, ofFin0, ofFin1, ofFin2, stopOK] at this
      refine ⟨fun h => ?_, fun h hw y hy => ?_⟩
      · simp only [cAct] at h; rw [h] at this; simpa using this
      · simp only [cAct] at h; rw [h] at this
        simp only [↓reduceIte] at this
        have h2 := this.2 hw
        simp only [chainOut] at hy
        split_ifs at hy h2 <;> simp only [mem_singleton] at hy <;> subst hy <;> exact h2
    · exact ⟨fun h => by simp [cAct] at h, fun _ _ y hy => by simp [chainOut] at hy⟩

open Classical in
lemma cCount {M : ℕ} (off pres : ℕ → Bool) (τ : Bool) :
    (univ.filter (fun w : CV M → Bool => cClosed off pres w ∧ w (topB M) = τ)).card =
      if τ then 1 else chainVal M (fun j => off j || !pres j) := by
  rw [← chain_count M pres off τ]
  refine card_nbij' (fun w => w ∘ (cvEquiv M).symm) (fun v => v ∘ (cvEquiv M)) ?_ ?_ ?_ ?_
  · intro w hw
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hw ⊢
    exact (cClosed_iff off pres τ w).1 hw
  · intro v hv
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv ⊢
    apply (cClosed_iff off pres τ _).2
    simpa [Function.comp] using hv
  · intro w _; funext x; simp
  · intro v _; funext x; simp

lemma cAct_true {M : ℕ} (x : CV M) : cAct (fun _ => true) x = true := by
  rcases x with ⟨j, r⟩ | j | j <;> rfl

open Classical in
lemma rCount {M : ℕ} (off : ℕ → Bool) (τ : Bool) :
    (univ.filter (fun w : CV M → Bool => rClosed off w ∧ w (topB M) = τ)).card =
      if τ then chainVal M off else 1 := by
  have h := cCount (M := M) off (fun _ => true) (!τ)
  have e2 : (fun j => off j || !(fun _ => true) j) = off := by funext j; simp
  rw [e2] at h
  have : (univ.filter (fun w : CV M → Bool => rClosed off w ∧ w (topB M) = τ)).card =
      (univ.filter (fun w : CV M → Bool => cClosed off (fun _ => true) w ∧ w (topB M) = !τ)).card := by
    refine card_nbij' (fun w x => !w x) (fun w x => !w x) ?_ ?_ ?_ ?_
    · intro w hw
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hw ⊢
      refine ⟨fun x => ⟨fun h => by rw [cAct_true] at h; exact absurd h (by simp),
        fun _ hx y hy => ?_⟩, by simp [hw.2]⟩
      have := hw.1 x y hy
      cases hwy : w y <;> cases hwx : w x <;> simp_all
    · intro w hw
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hw ⊢
      refine ⟨fun x y hy hwy => ?_, by cases τ <;> simp_all⟩
      have := (hw.1 x).2 (cAct_true x)
      cases hwx : w x <;> cases hwy' : w y <;> simp_all
    · intro w _; funext x; simp
    · intro w _; funext x; simp
  rw [this, h]; cases τ <;> rfl

lemma cClosed_top {M : ℕ} {off pres : ℕ → Bool} {w : CV M → Bool} (h : cClosed off pres w) :
    w (topC M) = w (topB M) := by
  have h1 := fun hw => (h (.lev (Fin.last M) .b)).2 rfl hw _ (mem_out_bc off (Fin.last M))
  have h2 := fun hw => (h (.lev (Fin.last M) .c)).2 rfl hw _ (mem_out_ca off (Fin.last M))
  have h3 := fun hw => (h (.lev (Fin.last M) .a)).2 rfl hw _ (mem_out_ab off (Fin.last M))
  exact bool_eq_of_imp (fun hc => h3 (h2 hc)) h1

lemma rClosed_top {M : ℕ} {off : ℕ → Bool} {w : CV M → Bool} (h : rClosed off w) :
    w (topC M) = w (topB M) := by
  have h1 := h _ _ (mem_out_bc off (Fin.last M))
  have h2 := h _ _ (mem_out_ca off (Fin.last M))
  have h3 := h _ _ (mem_out_ab off (Fin.last M))
  exact bool_eq_of_imp h1 (fun hb => h2 (h3 hb))

open Classical in
lemma card_split_top {α : Type*} [Fintype α] [DecidableEq α] (Q : (α → Bool) → Prop) (x : α)
    (P : Bool → Prop) :
    (univ.filter (fun w => Q w ∧ P (w x))).card =
      (if P true then (univ.filter (fun w => Q w ∧ w x = true)).card else 0) +
      (if P false then (univ.filter (fun w => Q w ∧ w x = false)).card else 0) := by
  rw [← card_filter_add_card_filter_not (p := fun w => w x = true)]
  simp only [filter_filter]
  congr 1
  · split_ifs with h
    · congr 1; ext w; simp only [mem_filter, mem_univ, true_and]; constructor
      · rintro ⟨⟨hq, _⟩, hw⟩; exact ⟨hq, hw⟩
      · rintro ⟨hq, hw⟩; exact ⟨⟨hq, by rw [hw]; exact h⟩, hw⟩
    · rw [card_eq_zero, filter_eq_empty_iff]; rintro w - ⟨⟨_, hp⟩, hw⟩; rw [hw] at hp; exact h hp
  · split_ifs with h
    · congr 1; ext w; simp only [mem_filter, mem_univ, true_and, Bool.not_eq_true]; constructor
      · rintro ⟨⟨hq, _⟩, hw⟩; exact ⟨hq, hw⟩
      · rintro ⟨hq, hw⟩; exact ⟨⟨hq, by rw [hw]; exact h⟩, hw⟩
    · rw [card_eq_zero, filter_eq_empty_iff]; rintro w - ⟨⟨_, hp⟩, hw⟩
      simp only [Bool.not_eq_true] at hw; rw [hw] at hp; exact h hp

open Classical in
lemma upCount {M : ℕ} (off : ℕ → Bool) (A B : Bool) :
    (univ.filter (fun w : CV M → Bool => cClosed off (fun _ => true) w ∧
      (A = true → w (topB M) = true) ∧ (B = true → w (topC M) = true))).card =
      if (A || B) = true then 1 else 1 + chainVal M off := by
  have h1 := cCount (M := M) off (fun _ => true) true
  have h0 := cCount (M := M) off (fun _ => true) false
  have e2 : (fun j => off j || !(fun _ => true) j) = off := by funext j; simp
  rw [e2] at h0
  simp only [if_true] at h1
  simp only [Bool.false_eq_true, if_false] at h0
  by_cases hAB : (A || B) = true
  · rw [if_pos hAB, ← h1]
    congr 1; ext w; simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hc, ha, hb⟩; refine ⟨hc, ?_⟩
      cases A
      · simp only [Bool.false_or] at hAB; rw [← cClosed_top hc]; exact hb hAB
      · exact ha rfl
    · rintro ⟨hc, ht⟩; exact ⟨hc, fun _ => ht, fun _ => by rw [cClosed_top hc]; exact ht⟩
  · have hA : A = false := by cases A <;> simp_all
    have hB : B = false := by cases B <;> simp_all
    subst hA; subst hB
    rw [if_neg hAB, ← h1, ← h0, ← card_union_of_disjoint]
    · congr 1; ext w; simp only [mem_filter, mem_univ, true_and, mem_union]
      constructor
      · rintro ⟨hc, -, -⟩; cases hw : w (topB M) <;> simp [hc]
      · rintro (⟨hc, -⟩ | ⟨hc, -⟩) <;> exact ⟨hc, by simp, by simp⟩
    · rw [disjoint_filter]; rintro w - ⟨-, h1⟩ ⟨-, h2⟩; rw [h1] at h2; exact absurd h2 (by simp)

open Classical in
lemma dnCount {M : ℕ} (off : ℕ → Bool) (A B : Bool) :
    (univ.filter (fun w : CV M → Bool => rClosed off w ∧
      (w (topB M) = true → A = true) ∧ (w (topC M) = true → B = true))).card =
      if (A && B) = true then 1 + chainVal M off else 1 := by
  have h1 := rCount (M := M) off true
  have h0 := rCount (M := M) off false
  simp only [if_true] at h1
  simp only [Bool.false_eq_true, if_false] at h0
  by_cases hAB : (A && B) = true
  · have hA : A = true := by cases A <;> simp_all
    have hB : B = true := by cases B <;> simp_all
    subst hA; subst hB
    rw [if_pos hAB, ← h1, ← h0, add_comm, ← card_union_of_disjoint]
    · congr 1; ext w; simp only [mem_filter, mem_univ, true_and, mem_union]
      constructor
      · rintro ⟨hc, -, -⟩; cases hw : w (topB M) <;> simp [hc]
      · rintro (⟨hc, -⟩ | ⟨hc, -⟩) <;> exact ⟨hc, by simp, by simp⟩
    · rw [disjoint_filter]; rintro w - ⟨-, h1⟩ ⟨-, h2⟩; rw [h1] at h2; exact absurd h2 (by simp)
  · rw [if_neg hAB, ← h0]
    congr 1; ext w; simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨hc, ha, hb⟩; refine ⟨hc, ?_⟩
      cases hw : w (topB M)
      · rfl
      · exfalso; apply hAB; simp only [Bool.and_eq_true]
        exact ⟨ha hw, hb (by rw [rClosed_top hc]; exact hw)⟩
    · rintro ⟨hc, ht⟩
      exact ⟨hc, fun h => by rw [ht] at h; exact absurd h (by simp),
        fun h => by rw [rClosed_top hc, ht] at h; exact absurd h (by simp)⟩

open Classical in
lemma ltCount (c s r : Bool) :
    (univ.filter (fun w : Unit → Bool =>
      if c = true then s = w () ∧ (w () = true → r = true) else w () = true)).card =
      if c = true ∧ s = true ∧ r = false then 0 else 1 := by
  rw [card_unit_fun (fun u => if c = true then s = u ∧ (u = true → r = true) else u = true)]
  cases c <;> cases s <;> cases r <;> simp

/-! The graph for parameters `n k q`. -/

abbrev Mq (q : ℕ) : ℕ := Nat.log2 q + (Nat.log2 q + 1)

def offC (q : ℕ) (j : ℕ) : Bool := if j < Nat.log2 q then q.testBit (Nat.log2 q - 1 - j) else false
def offU (q : ℕ) (j : ℕ) : Bool := if j < Nat.log2 q then q.testBit (Nat.log2 q - 1 - j)
  else (q - 1).testBit (Nat.log2 q + 1 - 1 - (j - Nat.log2 q))

def srcV {n k q : ℕ} : Vx n k (Mq q) → Option ((Fin k × Fin n × Bool) ⊕ (Fin k × Fin (Nat.log2 q + 1)))
  | .Lt e i b => some (Sum.inl (e, i, b))
  | .C e (.stp j) => if h : Nat.log2 q ≤ j.val then
      some (Sum.inr (e, ⟨Nat.log2 q + 1 - 1 - (j.val - Nat.log2 q), by omega⟩)) else none
  | .C _ (.lev _ _) => none
  | .C _ (.pnd _) => none
  | .T _ _ _ => none
  | .R _ _ _ => none
  | .N _ _ => none
  | .Ch _ _ _ _ => none

def actV {n k q : ℕ} (lit : Fin k → Fin n → Bool → Bool) (code : Fin k → ℕ) (v : Vx n k (Mq q)) : Bool :=
  (srcV v).elim true (Sum.elim (fun p => lit p.1 p.2.1 p.2.2) (fun p => !((code p.1).testBit p.2.val)))

def presC (q c : ℕ) (j : ℕ) : Bool :=
  if j < Nat.log2 q then true else !(c.testBit (Nat.log2 q + 1 - 1 - (j - Nat.log2 q)))

section main
variable {n k q : ℕ} (lit : Fin k → Fin n → Bool → Bool) (code : Fin k → ℕ)

lemma act_C (e : Fin k) (x : CV (Mq q)) :
    actV (n := n) lit code (Vx.C e x) = cAct (presC q (code e)) x := by
  rcases x with ⟨j, r⟩ | j | j
  · rfl
  · simp only [actV, srcV, cAct, presC]
    by_cases h : Nat.log2 q ≤ j.val
    · rw [dif_pos h, if_neg (by omega)]; rfl
    · rw [dif_neg h, if_pos (by omega)]; rfl
  · rfl

def PIc (σ : IF n k → Bool) : Prop :=
  (∀ i t r, σ (Sum.inl (i, t, r)) = σ (Sum.inl (i, 0, .a))) ∧
  (∀ e t r, σ (Sum.inr (Sum.inl (e, t, r))) = σ (Sum.inr (Sum.inl (e, 0, .a))))

def PBx (β : BK n k) (σ : IF n k → Bool) : (WB n k (Mq q) β → Bool) → Prop :=
  match β with
  | Sum.inl e => fun w => cClosed (M := Mq q) (offC q) (presC q (code e)) w ∧
      w (topB (Mq q)) = σ (Sum.inr (Sum.inl (e, Fin.last n, .b)))
  | Sum.inr (Sum.inl (e, i, b)) => fun w =>
      if lit e i b = true then
        (if b then σ (Sum.inl (i, e.castSucc, .b)) else σ (Sum.inr (Sum.inr (e, i)))) = w () ∧
        (w () = true → σ (Sum.inr (Sum.inl (e, i.castSucc, if b then .b else .b2))) = true)
      else w () = true
  | Sum.inr (Sum.inr (e, i, false)) => fun w => cClosed (M := Mq q) (offU q) (fun _ => true) w ∧
      (σ (Sum.inl (i, e.castSucc, .b2)) = true → w (topB (Mq q)) = true) ∧
      (σ (Sum.inr (Sum.inr (e, i))) = true → w (topC (Mq q)) = true)
  | Sum.inr (Sum.inr (e, i, true)) => fun w => rClosed (M := Mq q) (offU q) w ∧
      (w (topB (Mq q)) = true → σ (Sum.inl (i, e.castSucc, .b2)) = true) ∧
      (w (topC (Mq q)) = true → σ (Sum.inr (Sum.inr (e, i))) = true)

lemma track_const {K : ℕ} (f : Fin (K+1) → R4 → Bool)
    (hcyc : ∀ t, (f t .a = true → f t .b = true) ∧ (f t .b = true → f t .b2 = true) ∧
      (f t .b2 = true → f t .c = true) ∧ (f t .c = true → f t .a = true))
    (hlink : ∀ t : Fin K, (f t.castSucc .c = true → f t.succ .a = true) ∧
      (f t.succ .a = true → f t.castSucc .c = true)) :
    ∀ t r, f t r = f 0 .a := by
  have hlev : ∀ t r, f t r = f t .a := by
    intro t r
    obtain ⟨h1, h2, h3, h4⟩ := hcyc t
    rcases r with _ | _ | _ | _
    · rfl
    · exact bool_eq_of_imp (fun h => h4 (h3 (h2 h))) h1
    · exact bool_eq_of_imp (fun h => h4 (h3 h)) (fun h => h2 (h1 h))
    · exact bool_eq_of_imp h4 (fun h => h3 (h2 (h1 h)))
  have ha : ∀ t : Fin (K+1), f t .a = f 0 .a := by
    intro t
    induction t using Fin.induction with
    | zero => rfl
    | succ t ih =>
      rw [← ih, ← hlev t.castSucc .c]
      exact (bool_eq_of_imp (hlink t).1 (hlink t).2).symm
  intro t r; rw [hlev, ha]

section mems
variable {n k M : ℕ} (oU oC : ℕ → Bool)
lemma mT_ab (i : Fin n) (t : Fin (k+1)) : Vx.T (M := M) i t .b ∈ outN oU oC (Vx.T i t .a) := by
  simp only [outN]; split_ifs <;> simp
lemma mT_bb2 (i : Fin n) (t : Fin (k+1)) : Vx.T (M := M) i t .b2 ∈ outN oU oC (Vx.T i t .b) := by
  simp only [outN]; split_ifs <;> simp
lemma mT_b2c (i : Fin n) (t : Fin (k+1)) : Vx.T (M := M) i t .c ∈ outN oU oC (Vx.T i t .b2) := by
  simp only [outN]; split_ifs <;> simp
lemma mT_ca (i : Fin n) (t : Fin (k+1)) : Vx.T (M := M) i t .a ∈ outN oU oC (Vx.T i t .c) := by
  simp only [outN]; split_ifs <;> simp
lemma mT_l1 (i : Fin n) (t : Fin k) :
    Vx.T (M := M) i t.succ .a ∈ outN oU oC (Vx.T i t.castSucc .c) := by
  simp only [outN, Fin.val_castSucc]; rw [dif_pos t.isLt]; simp [Fin.ext_iff]
lemma mT_l2 (i : Fin n) (t : Fin k) :
    Vx.T (M := M) i t.castSucc .c ∈ outN oU oC (Vx.T i t.succ .a) := by
  simp only [outN, Fin.val_succ]; rw [dif_pos (by omega)]; simp [Fin.ext_iff]
lemma mR_ab (e : Fin k) (t : Fin (n+1)) : Vx.R (M := M) e t .b ∈ outN oU oC (Vx.R e t .a) := by
  simp only [outN]; split_ifs <;> simp
lemma mR_bb2 (e : Fin k) (t : Fin (n+1)) : Vx.R (M := M) e t .b2 ∈ outN oU oC (Vx.R e t .b) := by
  simp only [outN]; split_ifs <;> simp
lemma mR_b2c (e : Fin k) (t : Fin (n+1)) : Vx.R (M := M) e t .c ∈ outN oU oC (Vx.R e t .b2) := by
  simp [outN]
lemma mR_ca (e : Fin k) (t : Fin (n+1)) : Vx.R (M := M) e t .a ∈ outN oU oC (Vx.R e t .c) := by
  simp only [outN]; split_ifs <;> simp
lemma mR_l1 (e : Fin k) (t : Fin n) :
    Vx.R (M := M) e t.succ .a ∈ outN oU oC (Vx.R e t.castSucc .c) := by
  simp only [outN, Fin.val_castSucc]; rw [dif_pos t.isLt]; simp [Fin.ext_iff]
lemma mR_l2 (e : Fin k) (t : Fin n) :
    Vx.R (M := M) e t.castSucc .c ∈ outN oU oC (Vx.R e t.succ .a) := by
  simp only [outN, Fin.val_succ]; rw [dif_pos (by omega)]; simp [Fin.ext_iff]
end mems

lemma toSum_ofSum {n k M : ℕ} (z : SV n k M) : toSum (ofSum z) = z := (vxEquiv n k M).right_inv z

lemma closed_iff (u : SV n k (Mq q) → Bool) :
    ((∀ x, actV lit code x = false → u (toSum x) = true) ∧
      ∀ x y, y ∈ outN (offU q) (offC q) x → actV lit code x = true → u (toSum x) = true →
        u (toSum y) = true) ↔
    (PIc (fun a => u (Sum.inl a)) ∧
      ∀ β, PBx lit code β (fun a => u (Sum.inl a)) (fun x => u (Sum.inr ⟨β, x⟩))) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hE : ∀ x y, y ∈ outN (offU q) (offC q) x → actV lit code x = true →
        u (toSum x) = true → u (toSum y) = true := h2
    refine ⟨⟨fun i => ?_, fun e => ?_⟩, fun β => ?_⟩
    · exact track_const (fun t r => u (Sum.inl (Sum.inl (i, t, r))))
        (fun t => ⟨hE _ _ (mT_ab _ _ i t) rfl, hE _ _ (mT_bb2 _ _ i t) rfl,
          hE _ _ (mT_b2c _ _ i t) rfl, hE _ _ (mT_ca _ _ i t) rfl⟩)
        (fun t => ⟨hE _ _ (mT_l1 _ _ i t) rfl, hE _ _ (mT_l2 _ _ i t) rfl⟩)
    · exact track_const (fun t r => u (Sum.inl (Sum.inr (Sum.inl (e, t, r)))))
        (fun t => ⟨hE _ _ (mR_ab _ _ e t) rfl, hE _ _ (mR_bb2 _ _ e t) rfl,
          hE _ _ (mR_b2c _ _ e t) rfl, hE _ _ (mR_ca _ _ e t) rfl⟩)
        (fun t => ⟨hE _ _ (mR_l1 _ _ e t) rfl, hE _ _ (mR_l2 _ _ e t) rfl⟩)
    · rcases β with e | ⟨e, i, b⟩ | ⟨e, i, d⟩
      · simp only [PBx]
        refine ⟨fun x => ⟨fun hx => h1 (Vx.C e x) (by rw [act_C]; exact hx),
          fun hx hw y hy => hE (Vx.C e x) (Vx.C e y) ?_ (by rw [act_C]; exact hx) hw⟩, ?_⟩
        · simp only [outN]; exact mem_union_left _ (mem_image_of_mem _ hy)
        · apply bool_eq_of_imp
          · exact hE (Vx.C e (topB _)) (Vx.R e (Fin.last n) .b) (by simp [outN]) rfl
          · exact hE (Vx.R e (Fin.last n) .b) (Vx.C e (topB _)) (by simp [outN]) rfl
      · cases b
        · show (if lit e i false = true then u (toSum (Vx.N e i)) = u (toSum (Vx.Lt e i false)) ∧
              (u (toSum (Vx.Lt e i false)) = true → u (toSum (Vx.R e i.castSucc .b2)) = true)
            else u (toSum (Vx.Lt e i false)) = true)
          split_ifs with hl
          · exact ⟨bool_eq_of_imp (hE _ _ (by simp [outN]) rfl) (hE _ _ (by simp [outN]) hl),
              hE _ _ (by simp [outN]) hl⟩
          · exact h1 _ (by simpa [actV, srcV] using hl)
        · show (if lit e i true = true then
              u (toSum (Vx.T i e.castSucc .b)) = u (toSum (Vx.Lt e i true)) ∧
              (u (toSum (Vx.Lt e i true)) = true → u (toSum (Vx.R e i.castSucc .b)) = true)
            else u (toSum (Vx.Lt e i true)) = true)
          split_ifs with hl
          · refine ⟨bool_eq_of_imp (hE _ _ ?_ rfl) (hE _ _ (by simp [outN]) hl),
              hE _ _ (by simp [outN]) hl⟩
            simp only [outN, Fin.val_castSucc]; rw [dif_pos e.isLt]; simp
          · exact h1 _ (by simpa [actV, srcV] using hl)
      · cases d
        · simp only [PBx]
          refine ⟨fun x => ⟨fun hx => by rw [cAct_true] at hx; exact absurd hx (by simp),
            fun _ hw y hy => hE (Vx.Ch e i false x) (Vx.Ch e i false y) ?_ rfl hw⟩, ?_, ?_⟩
          · simp only [outN]; exact mem_image_of_mem _ hy
          · refine hE (Vx.T i e.castSucc .b2) (Vx.Ch e i false (topB _)) ?_ rfl
            simp only [outN, Fin.val_castSucc]; rw [dif_pos e.isLt]; simp
          · exact hE (Vx.N e i) (Vx.Ch e i false (topC _)) (by simp [outN]) rfl
        · simp only [PBx]
          refine ⟨fun x y hy hw => hE (Vx.Ch e i true y) (Vx.Ch e i true x) ?_ rfl hw, ?_, ?_⟩
          · simp only [outN]; exact mem_union_left _ (mem_image_of_mem _ (by simpa using hy))
          · exact hE (Vx.Ch e i true (topB _)) (Vx.T i e.castSucc .b2) (by simp [outN]) rfl
          · exact hE (Vx.Ch e i true (topC _)) (Vx.N e i) (by simp [outN, (topB_ne_topC _).symm]) rfl
  · rintro ⟨⟨hT, hR⟩, hB⟩
    have hTe : ∀ i t r t' r', u (Sum.inl (Sum.inl (i, t, r))) = u (Sum.inl (Sum.inl (i, t', r'))) :=
      fun i t r t' r' => (hT i t r).trans (hT i t' r').symm
    have hRe : ∀ e t r t' r', u (Sum.inl (Sum.inr (Sum.inl (e, t, r)))) =
        u (Sum.inl (Sum.inr (Sum.inl (e, t', r')))) :=
      fun e t r t' r' => (hR e t r).trans (hR e t' r').symm
    refine ⟨fun x hx => ?_, fun x y hxy hx hv => ?_⟩
    · rcases x with ⟨i, t, r⟩ | ⟨e, t, r⟩ | ⟨e, i⟩ | ⟨e, w⟩ | ⟨e, i, b⟩ | ⟨e, i, d, w⟩
      · exact absurd hx (by simp [actV, srcV])
      · exact absurd hx (by simp [actV, srcV])
      · exact absurd hx (by simp [actV, srcV])
      · have := (hB (Sum.inl e)).1 w
        rw [act_C] at hx
        exact this.1 hx
      · have := hB (Sum.inr (Sum.inl (e, i, b)))
        simp only [PBx] at this
        have hl : lit e i b = false := by simpa [actV, srcV] using hx
        rw [if_neg (by simp [hl])] at this
        exact this
      · exact absurd hx (by simp [actV, srcV])
    · rcases x with ⟨i, t, r⟩ | ⟨e, t, r⟩ | ⟨e, i⟩ | ⟨e, w⟩ | ⟨e, i, b⟩ | ⟨e, i, d, w⟩
      · -- track vertex
        have ht := t.isLt
        rcases r with _ | _ | _ | _ <;> simp only [outN] at hxy <;> (try split_ifs at hxy with h1) <;>
          simp only [mem_insert, mem_singleton] at hxy
        · rcases hxy with rfl | rfl <;> (show u (Sum.inl (Sum.inl _)) = true) <;> rw [hTe] <;> exact hv
        · subst hxy; show u (Sum.inl (Sum.inl _)) = true; rw [hTe]; exact hv
        · rcases hxy with rfl | rfl
          · show u (Sum.inl (Sum.inl _)) = true; rw [hTe]; exact hv
          · have := hB (Sum.inr (Sum.inl (⟨t, h1⟩, i, true)))
            simp only [PBx, ↓reduceIte] at this
            split_ifs at this with hl
            · exact this.1.symm.trans hv
            · exact this
        · subst hxy; show u (Sum.inl (Sum.inl _)) = true; rw [hTe]; exact hv
        · rcases hxy with rfl | rfl
          · show u (Sum.inl (Sum.inl _)) = true; rw [hTe]; exact hv
          · have := hB (Sum.inr (Sum.inr (⟨t, h1⟩, i, false)))
            simp only [PBx] at this
            exact this.2.1 hv
        · subst hxy; show u (Sum.inl (Sum.inl _)) = true; rw [hTe]; exact hv
        · rcases hxy with rfl | rfl <;> (show u (Sum.inl (Sum.inl _)) = true) <;> rw [hTe] <;> exact hv
        · subst hxy; show u (Sum.inl (Sum.inl _)) = true; rw [hTe]; exact hv
      · -- ring vertex
        have ht := t.isLt
        rcases r with _ | _ | _ | _ <;> simp only [outN] at hxy <;> (try split_ifs at hxy with h1) <;>
          simp only [mem_insert, mem_singleton] at hxy
        · rcases hxy with rfl | rfl <;> (show u (Sum.inl (Sum.inr (Sum.inl _))) = true) <;>
            rw [hRe] <;> exact hv
        · subst hxy; show u (Sum.inl (Sum.inr (Sum.inl _))) = true; rw [hRe]; exact hv
        · rcases hxy with rfl | rfl
          · show u (Sum.inl (Sum.inr (Sum.inl _))) = true; rw [hRe]; exact hv
          · have := (hB (Sum.inl e)).2
            have htl : t = Fin.last n := Fin.ext h1
            subst htl
            exact this.trans hv
        · subst hxy; show u (Sum.inl (Sum.inr (Sum.inl _))) = true; rw [hRe]; exact hv
        · subst hxy; show u (Sum.inl (Sum.inr (Sum.inl _))) = true; rw [hRe]; exact hv
        · rcases hxy with rfl | rfl <;> (show u (Sum.inl (Sum.inr (Sum.inl _))) = true) <;>
            rw [hRe] <;> exact hv
        · subst hxy; show u (Sum.inl (Sum.inr (Sum.inl _))) = true; rw [hRe]; exact hv
      · -- negation vertex
        simp only [outN, mem_insert, mem_singleton] at hxy
        rcases hxy with rfl | rfl
        · exact (hB (Sum.inr (Sum.inr (e, i, false)))).2.2 hv
        · have := hB (Sum.inr (Sum.inl (e, i, false)))
          simp only [PBx, Bool.false_eq_true, ↓reduceIte] at this
          split_ifs at this with hl
          · exact this.1.symm.trans hv
          · exact this
      · -- counter chain
        have hc := (hB (Sum.inl e)).1
        have htop := (hB (Sum.inl e)).2
        rw [act_C] at hx
        simp only [outN, mem_union, mem_image] at hxy
        rcases hxy with ⟨y', hy', rfl⟩ | hxy
        · exact (hc w).2 hx hv y' hy'
        · split_ifs at hxy with hw
          · subst hw; simp only [mem_singleton] at hxy; subst hxy
            exact htop.symm.trans hv
          · simp at hxy
      · -- literal vertex
        have hl : lit e i b = true := by simpa [actV, srcV] using hx
        have := hB (Sum.inr (Sum.inl (e, i, b)))
        simp only [PBx] at this
        rw [if_pos hl] at this
        cases b
        · simp only [outN, mem_insert, mem_singleton] at hxy
          simp only [Bool.false_eq_true, ↓reduceIte] at this
          rcases hxy with rfl | rfl
          · exact this.1.trans hv
          · exact this.2 hv
        · simp only [outN, mem_insert, mem_singleton] at hxy
          simp only [↓reduceIte] at this
          rcases hxy with rfl | rfl
          · exact this.1.trans hv
          · exact this.2 hv
      · -- negation chains
        cases d
        · have hc := (hB (Sum.inr (Sum.inr (e, i, false)))).1
          simp only [outN, mem_image] at hxy
          obtain ⟨y', hy', rfl⟩ := hxy
          exact (hc w).2 (cAct_true w) hv y' hy'
        · have hB' := hB (Sum.inr (Sum.inr (e, i, true)))
          simp only [PBx] at hB'
          simp only [outN, mem_union, mem_image, mem_filter, mem_univ, true_and] at hxy
          rcases hxy with ⟨y', hy', rfl⟩ | hxy
          · exact hB'.1 y' w hy' hv
          · split_ifs at hxy with hw hw'
            · subst hw; simp only [mem_singleton] at hxy; subst hxy; exact hB'.2.1 hv
            · subst hw'; simp only [mem_singleton] at hxy; subst hxy; exact hB'.2.2 hv
            · simp at hxy

end main

end count

/-! ### Assembling the count -/

section assemble

lemma ofSum_toSum {n k M : ℕ} (x : Vx n k M) : ofSum (toSum x) = x := (vxEquiv n k M).left_inv x

def liftσ {n k : ℕ} (x : (Fin n → Bool) × (Fin k → Bool) × (Fin k → Fin n → Bool)) : IF n k → Bool
  | Sum.inl (i, _, _) => x.1 i
  | Sum.inr (Sum.inl (e, _, _)) => x.2.1 e
  | Sum.inr (Sum.inr (e, i)) => x.2.2 e i

def projσ {n k : ℕ} (σ : IF n k → Bool) : (Fin n → Bool) × (Fin k → Bool) × (Fin k → Fin n → Bool) :=
  (fun i => σ (Sum.inl (i, 0, .a)), fun e => σ (Sum.inr (Sum.inl (e, 0, .a))),
    fun e i => σ (Sum.inr (Sum.inr (e, i))))

open Classical in
lemma reindex {n k : ℕ} {R : Type*} [AddCommMonoid R] (F : (IF n k → Bool) → R) :
    ∑ σ : IF n k → Bool, (if PIc σ then F σ else 0) = ∑ x, F (liftσ x) := by
  rw [← Finset.sum_filter]
  have key : ∀ σ : IF n k → Bool, PIc σ → liftσ (projσ σ) = σ := by
    intro σ hσ
    funext a
    rcases a with ⟨i, t, r⟩ | ⟨e, t, r⟩ | ⟨e, i⟩
    · exact (hσ.1 i t r).symm
    · exact (hσ.2 e t r).symm
    · rfl
  apply Finset.sum_nbij' projσ liftσ
  · intro σ _; exact mem_univ _
  · intro x _; simp only [mem_filter, mem_univ, true_and]; exact ⟨fun i t r => rfl, fun e t r => rfl⟩
  · intro σ hσ; simp only [mem_filter, mem_univ, true_and] at hσ; exact key σ hσ
  · intro x _; rfl
  · intro σ hσ; simp only [mem_filter, mem_univ, true_and] at hσ; rw [key σ hσ]

lemma alg_core {R : Type*} [CommRing R] (n k : ℕ) (cT : Fin k → Bool → R)
    (K : Fin k → Fin n → Bool → Bool → R) :
    ∑ τ : Fin k → Bool, ∑ ν : Fin k → Fin n → Bool, ∏ e, (cT e (τ e) * ∏ i, K e i (τ e) (ν e i)) =
    ∏ e, ∑ t : Bool, cT e t * ∏ i, ∑ b : Bool, K e i t b := by
  calc ∑ τ : Fin k → Bool, ∑ ν : Fin k → Fin n → Bool, ∏ e, (cT e (τ e) * ∏ i, K e i (τ e) (ν e i))
      = ∑ τ : Fin k → Bool, ∏ e, ∑ νe : Fin n → Bool, (cT e (τ e) * ∏ i, K e i (τ e) (νe i)) := by
        refine Finset.sum_congr rfl (fun τ _ => ?_)
        rw [Fintype.prod_sum (fun e (νe : Fin n → Bool) => cT e (τ e) * ∏ i, K e i (τ e) (νe i))]
    _ = ∏ e, ∑ t : Bool, ∑ νe : Fin n → Bool, (cT e t * ∏ i, K e i t (νe i)) := by
        rw [Fintype.prod_sum (fun e (t : Bool) => ∑ νe : Fin n → Bool, (cT e t * ∏ i, K e i t (νe i)))]
    _ = ∏ e, ∑ t : Bool, cT e t * ∏ i, ∑ b : Bool, K e i t b := by
        refine Finset.prod_congr rfl (fun e _ => Finset.sum_congr rfl (fun t _ => ?_))
        rw [← Finset.mul_sum, Fintype.prod_sum (fun i (b : Bool) => K e i t b)]

lemma alg_main {R : Type*} [CommRing R] (n k : ℕ) (cT : Fin k → Bool → R)
    (L : Fin k → Fin n → Bool → Bool → Bool → R) (U D : Bool → Bool → R) (y : Fin n → Bool) :
    ∑ τ : Fin k → Bool, ∑ ν : Fin k → Fin n → Bool,
      (∏ e, cT e (τ e)) * ((∏ p : Fin k × Fin n × Bool,
        L p.1 p.2.1 p.2.2 (if p.2.2 then y p.2.1 else ν p.1 p.2.1) (τ p.1)) *
        (∏ p : Fin k × Fin n × Bool,
          if p.2.2 then D (y p.2.1) (ν p.1 p.2.1) else U (y p.2.1) (ν p.1 p.2.1))) =
    ∏ e, ∑ t : Bool, cT e t * ∏ i, ∑ b : Bool,
      (L e i true (y i) t * L e i false b t * (U (y i) b * D (y i) b)) := by
  rw [← alg_core]
  refine Finset.sum_congr rfl (fun τ _ => Finset.sum_congr rfl (fun ν _ => ?_))
  simp only [Fintype.prod_prod_type, Fintype.prod_bool, if_true, Bool.false_eq_true, if_false,
    Finset.prod_mul_distrib]
  ring

lemma clause_val {R : Type*} [CommRing R] (V c : R) (hV : 1 + V = 0) (n : ℕ)
    (lt lf y : Fin n → Bool) :
    ∑ t : Bool, (if t = true then 1 else c) * ∏ i : Fin n, ∑ b : Bool,
      ((if lt i = true ∧ y i = true ∧ t = false then (0 : R) else 1) *
        (if lf i = true ∧ b = true ∧ t = false then (0 : R) else 1) *
        ((if (y i || b) = true then (1 : R) else 1 + V) * (if (y i && b) = true then 1 + V else (1 : R)))) =
    if ∀ i, (if y i = true then lt i else lf i) = false then 1 + c else 1 := by
  have hin : ∀ (t : Bool) (i : Fin n), ∑ b : Bool,
      ((if lt i = true ∧ y i = true ∧ t = false then (0 : R) else 1) *
        (if lf i = true ∧ b = true ∧ t = false then (0 : R) else 1) *
        ((if (y i || b) = true then (1 : R) else 1 + V) * (if (y i && b) = true then 1 + V else (1 : R)))) =
      if t = false ∧ (if y i = true then lt i else lf i) = true then 0 else 1 := by
    intro t i
    rw [Fintype.sum_bool]
    cases t <;> cases hy : y i <;> cases lt i <;> cases lf i <;> simp [hV]
  simp only [hin, Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, true_and, false_and,
    and_false, Finset.prod_const_one, mul_one, Bool.true_eq_false]
  by_cases h : ∀ i, (if y i = true then lt i else lf i) = false
  · rw [if_pos h]
    simp [h]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨i, hi⟩ := h
    have hi' : (if y i = true then lt i else lf i) = true := by simpa using hi
    have hz : (∏ x : Fin n, (if (if y x = true then lt x else lf x) = true then (0:R) else 1)) = 0 :=
      Finset.prod_eq_zero (mem_univ i) (by rw [hi']; simp)
    rw [hz]
    simp

open Classical in
lemma blkC {n k q : ℕ} (lit : Fin k → Fin n → Bool → Bool) (code : Fin k → ℕ)
    (x : (Fin n → Bool) × (Fin k → Bool) × (Fin k → Fin n → Bool)) (e : Fin k) :
    (univ.filter (PBx (q := q) lit code (Sum.inl e) (liftσ x))).card =
      if x.2.1 e = true then 1 else chainVal (Mq q) (fun j => offC q j || !presC q (code e) j) := by
  refine Eq.trans ?_ (cCount (M := Mq q) (offC q) (presC q (code e)) (x.2.1 e))
  refine card_nbij' id id ?_ ?_ ?_ ?_
  · intro w hw; simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hw ⊢; exact hw
  · intro w hw; simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hw ⊢; exact hw
  · intro w _; rfl
  · intro w _; rfl

open Classical in
lemma blkLt {n k q : ℕ} (lit : Fin k → Fin n → Bool → Bool) (code : Fin k → ℕ)
    (x : (Fin n → Bool) × (Fin k → Bool) × (Fin k → Fin n → Bool)) (p : Fin k × Fin n × Bool) :
    (univ.filter (PBx (q := q) lit code (Sum.inr (Sum.inl p)) (liftσ x))).card =
      if lit p.1 p.2.1 p.2.2 = true ∧ (if p.2.2 then x.1 p.2.1 else x.2.2 p.1 p.2.1) = true ∧
        x.2.1 p.1 = false then 0 else 1 := by
  obtain ⟨e, i, b⟩ := p
  rw [← ltCount]
  cases b
  · refine card_nbij' id id ?_ ?_ ?_ ?_
    · intro w hw; simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hw ⊢; exact hw
    · intro w hw; simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hw ⊢; exact hw
    · intro w _; rfl
    · intro w _; rfl
  · refine card_nbij' id id ?_ ?_ ?_ ?_
    · intro w hw; simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hw ⊢; exact hw
    · intro w hw; simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hw ⊢; exact hw
    · intro w _; rfl
    · intro w _; rfl

open Classical in
lemma blkCh {n k q : ℕ} (lit : Fin k → Fin n → Bool → Bool) (code : Fin k → ℕ)
    (x : (Fin n → Bool) × (Fin k → Bool) × (Fin k → Fin n → Bool)) (p : Fin k × Fin n × Bool) :
    (univ.filter (PBx (q := q) lit code (Sum.inr (Sum.inr p)) (liftσ x))).card =
      if p.2.2 then
        (if (x.1 p.2.1 && x.2.2 p.1 p.2.1) = true then 1 + chainVal (Mq q) (offU q) else 1)
      else (if (x.1 p.2.1 || x.2.2 p.1 p.2.1) = true then 1 else 1 + chainVal (Mq q) (offU q)) := by
  obtain ⟨e, i, (_ | _)⟩ := p
  · simp only [Bool.false_eq_true, if_false, ↓reduceIte]
    refine Eq.trans ?_ (upCount (M := Mq q) (offU q) (x.1 i) (x.2.2 e i))
    refine card_nbij' id id ?_ ?_ ?_ ?_
    · intro w hw; simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hw ⊢; exact hw
    · intro w hw; simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hw ⊢; exact hw
    · intro w _; rfl
    · intro w _; rfl
  · simp only [if_true, ↓reduceIte]
    refine Eq.trans ?_ (dnCount (M := Mq q) (offU q) (x.1 i) (x.2.2 e i))
    refine card_nbij' id id ?_ ?_ ?_ ?_
    · intro w hw; simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hw ⊢; exact hw
    · intro w hw; simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hw ⊢; exact hw
    · intro w _; rfl
    · intro w _; rfl

open Classical in
lemma count_main {n k q : ℕ} (hq : 2 ≤ q) (lit : Fin k → Fin n → Bool → Bool) (weight : Fin k → Fin q) :
    (((univ.filter (fun v : Vx n k (Mq q) → Bool =>
      (∀ x, actV lit (fun e => ((weight e).val + q - 1) % q) x = false → v x = true) ∧
      ∀ x y, y ∈ outN (offU q) (offC q) x →
        actV lit (fun e => ((weight e).val + q - 1) % q) x = true → v x = true → v y = true)).card :
        ℕ) : ZMod q) =
    (((∑ y : Fin n → Bool, ∏ e : Fin k,
      if ∀ i, lit e i (y i) = false then (weight e).val else 1 : ℕ)) : ZMod q) := by
  set code : Fin k → ℕ := fun e => ((weight e).val + q - 1) % q with hcode
  have hA : (univ.filter (fun v : Vx n k (Mq q) → Bool =>
      (∀ x, actV lit code x = false → v x = true) ∧
      ∀ x y, y ∈ outN (offU q) (offC q) x → actV lit code x = true → v x = true → v y = true)).card =
      (univ.filter (fun u : SV n k (Mq q) → Bool => PIc (fun a => u (Sum.inl a)) ∧
        ∀ β, PBx lit code β (fun a => u (Sum.inl a)) (fun x => u (Sum.inr ⟨β, x⟩)))).card := by
    refine card_nbij' (fun v => v ∘ ofSum) (fun u => u ∘ toSum) ?_ ?_ ?_ ?_
    · intro v hv
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv ⊢
      apply (closed_iff lit code (v ∘ ofSum)).1
      simpa [Function.comp, ofSum_toSum] using hv
    · intro u hu
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hu ⊢
      exact (closed_iff lit code u).2 hu
    · intro v _; funext x; simp [ofSum_toSum]
    · intro u _; funext z; simp [toSum_ofSum]
  rw [hA]
  have hsplit := card_split (PIc (n := n) (k := k)) (PBx (q := q) lit code)
  rw [show (univ.filter (fun u : SV n k (Mq q) → Bool => PIc (fun a => u (Sum.inl a)) ∧
        ∀ β, PBx lit code β (fun a => u (Sum.inl a)) (fun x => u (Sum.inr ⟨β, x⟩)))).card =
      ∑ σ : IF n k → Bool, (if PIc σ then ∏ β, (univ.filter (PBx lit code β σ)).card else 0) by
    convert hsplit using 4]
  rw [reindex]
  simp only [Fintype.prod_sum_type, blkC, blkLt, blkCh]
  have hql : q < 2 ^ (Nat.log2 q + 1) := Nat.lt_log2_self
  have hVval : chainVal (Mq q) (offU q) = 2 ^ (Nat.log2 q + 1) * q + (q - 1) := by
    apply counter_val q (q - 1) hq (by omega)
    · intro j hj; simp [offU, hj]
    · intro j hj; simp [offU]
  have hCval : ∀ e, chainVal (Mq q) (fun j => offC q j || !presC q (code e) j) =
      2 ^ (Nat.log2 q + 1) * q + code e := by
    intro e
    apply counter_val q (code e) hq
    · have : code e < q := Nat.mod_lt _ (by omega)
      omega
    · intro j hj; simp [offC, presC, hj]
    · intro j hj; simp [offC, presC]
  simp only [hCval]
  set Vu := chainVal (Mq q) (offU q) with hVu
  have hV : (1 : ZMod q) + (Vu : ZMod q) = 0 := by
    rw [hVval, ← Nat.cast_one, ← Nat.cast_add,
      show 1 + (2 ^ (Nat.log2 q + 1) * q + (q - 1)) = 2 ^ (Nat.log2 q + 1) * q + q by omega]
    simp [ZMod.natCast_self]
  have h1code : ∀ e, (1 : ZMod q) + (code e : ZMod q) = ((weight e).val : ZMod q) := by
    intro e
    show (1 : ZMod q) + ((((weight e).val + q - 1) % q : ℕ) : ZMod q) = _
    rw [ZMod.natCast_mod, ← Nat.cast_one, ← Nat.cast_add,
      show 1 + ((weight e).val + q - 1) = (weight e).val + q by omega, Nat.cast_add,
      ZMod.natCast_self, add_zero]
  push_cast
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Fintype.sum_prod_type]
  have key := alg_main (R := ZMod q) n k (fun e t => if t = true then 1 else (code e : ZMod q))
    (fun e i b s t => if lit e i b = true ∧ s = true ∧ t = false then 0 else 1)
    (fun s b => if (s || b) = true then 1 else 1 + (Vu : ZMod q))
    (fun s b => if (s && b) = true then 1 + (Vu : ZMod q) else 1) y
  refine Eq.trans ?_ (key.trans ?_)
  · refine Finset.sum_congr rfl (fun τ _ => Finset.sum_congr rfl (fun ν _ => ?_))
    congr 1
    all_goals try (refine Finset.prod_congr rfl (fun e _ => ?_); simp; done)
    all_goals try (congr 1)
    all_goals try (refine Finset.prod_congr rfl (fun p _ => ?_); simp; done)
    all_goals (refine Finset.prod_congr rfl (fun p _ => ?_); obtain ⟨e, i, b⟩ := p; cases b <;> simp)
  · refine Finset.prod_congr rfl (fun e _ => ?_)
    refine (clause_val (Vu : ZMod q) (code e : ZMod q) hV n (fun i => lit e i true)
      (fun i => lit e i false) y).trans ?_
    have hcond : ∀ i, (if y i = true then lit e i true else lit e i false) = lit e i (y i) := by
      intro i; cases y i <;> rfl
    simp only [hcond]
    split_ifs <;> simp [h1code]

lemma card_CV (M : ℕ) : Fintype.card (CV M) = 5 * M + 3 := by
  rw [Fintype.card_congr (cvEquiv M)]
  simp only [ChainV, Fintype.card_sum, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_unit, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  ring

lemma card_R4 : Fintype.card R4 = 4 := rfl

lemma card_Vx (n k M : ℕ) : Fintype.card (Vx n k M) =
    n * ((k+1) * 4) + (k * ((n+1) * 4) + k * n) +
      (k * (5 * M + 3) + (k * (n * 2) + k * (n * 2) * (5 * M + 3))) := by
  rw [Fintype.card_congr (vxEquiv n k M)]
  have h1 : ∀ e, Fintype.card (WB n k M (Sum.inl e)) = 5 * M + 3 := fun e => card_CV M
  have h2 : ∀ p, Fintype.card (WB n k M (Sum.inr (Sum.inl p))) = 1 := fun p => rfl
  have h3 : ∀ p, Fintype.card (WB n k M (Sum.inr (Sum.inr p))) = 5 * M + 3 := fun p => card_CV M
  simp only [SV, IF, BK, Fintype.card_sum, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin,
    card_R4, Fintype.card_bool, Fintype.sum_sum_type, h1, h2, h3, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one]
  all_goals ring

theorem cons_ok (n k q : ℕ) (hq : 2 ≤ q) : Nonempty (Cons n k q) := by
  classical
  let eV := Fintype.equivFin (Vx n k (Mq q))
  have hcard := card_Vx n k (Mq q)
  exact ⟨{
    m := Fintype.card (Vx n k (Mq q))
    E := fun i j => decide (eV.symm j ∈ outN (offU q) (offC q) (eV.symm i))
    source := fun i => srcV (eV.symm i)
    lo := fun i => lo (eV.symm i)
    hi := fun i => hi (eV.symm i)
    l := enc n (Mq q) k 0 n
    size := by
      rw [hcard]; simp only [Mq]; ring_nf; nlinarith [Nat.zero_le (n * k * Nat.log2 q),
        Nat.zero_le (n * k), Nat.zero_le (k * Nat.log2 q), Nat.zero_le (n * Nat.log2 q)]
    irrefl := fun i => by simp [outN_irrefl]
    outdeg := fun i => by
      refine le_trans (card_le_card_of_injOn (fun j => eV.symm j) ?_ ?_) (card_outN (offU q) (offC q) (eV.symm i))
      · intro j hj; simpa using hj
      · intro a _ b _ h; exact eV.symm.injective h
    indeg := fun j => by
      refine le_trans (card_le_card_of_injOn (fun i => eV.symm i) ?_ ?_) (card_inN (offU q) (offC q) (eV.symm j))
      · intro i hi
        have : eV.symm j ∈ outN (offU q) (offC q) (eV.symm i) := by simpa using hi
        simpa using out_in _ _ _ _ this
      · intro a _ b _ h; exact eV.symm.injective h
    len := by
      rw [hcard]; unfold enc PP; simp only [Mq]; ring_nf; nlinarith [Nat.zero_le (n * k * Nat.log2 q),
        Nat.zero_le (n * k), Nat.zero_le (k * Nat.log2 q), Nat.zero_le (n * Nat.log2 q)]
    lohi := fun i => lo_le_hi _
    hil := fun i => hi_lt _
    edge := fun i j h => edge_ok _ _ _ _ (by simpa using h)
    width := fun t => by
      refine le_trans (card_le_card_of_injOn (fun i => eV.symm i) ?_ ?_) (width (n := n) (k := k) (M := Mq q) t)
      · intro i hi; simpa using hi
      · intro a _ b _ h; exact eV.symm.injective h
    count := fun lit weight => by
      rw [← ZMod.natCast_eq_natCast_iff']
      refine Eq.trans ?_ ((count_main hq lit weight).trans ?_)
      · congr 1
        refine card_nbij' (fun v => v ∘ eV) (fun w => w ∘ eV.symm) ?_ ?_ ?_ ?_
        · intro v hv
          simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv ⊢
          refine ⟨fun x hx => ?_, fun x y hxy hx hv' => ?_⟩
          · have := hv.1 (eV x)
            simp only [Equiv.symm_apply_apply] at this
            exact this hx
          · have := hv.2 (eV x) (eV y)
            simp only [Equiv.symm_apply_apply, decide_eq_true_eq] at this
            exact this hxy hx hv'
        · intro w hw
          simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hw ⊢
          exact ⟨fun i hi => hw.1 _ hi, fun i j hij hi hv => hw.2 _ _ (by simpa using hij) hi hv⟩
        · intro v _; funext i; simp
        · intro w _; funext x; simp
      · first | rfl | simp }⟩

end assemble

end PEqualNP.Outside.L_lib_1210_aux
theorem PEqualNP.Outside.L_lib_1210 :
    letI : ∀ p : Prop, Decidable p := Classical.propDecidable
    ∀ n k q : Nat, 2 ≤ q →
      let L := Nat.log2 q + 1
      ∃ (m : Nat) (nb : (Fin m × Bool) → Finset (Fin m × Bool))
        (source : Fin m → Option ((Fin k × Fin n × Bool) ⊕ (Fin k × Fin L))),
        m ≤ 200*(n+1)*(k+1)*(L+1) ∧
        (∀ p, p ∉ nb p ∧ (nb p).card ≤ 3) ∧
        (∀ p r, r ∈ nb p ↔ p ∈ nb r) ∧ (∀ p, ∀ r ∈ nb p, p.2 ≠ r.2) ∧
        (∀ i, (i,true) ∈ nb (i,false)) ∧
        (∃ (l : Nat) (bag : Fin l → Finset (Fin m)),
          l ≤ 2*m+1 ∧ (∀ t, (bag t).card ≤ n+11) ∧ (∀ i, ∃ t, i ∈ bag t) ∧
          (∀ i j, i ≠ j → (∃ a b : Bool, (j,b) ∈ nb (i,a)) →
            ∃ t, i ∈ bag t ∧ j ∈ bag t) ∧
          ∀ i s t u, s ≤ t → t ≤ u → i ∈ bag s → i ∈ bag u → i ∈ bag t) ∧
        ∀ (lit : Fin k → Fin n → Bool → Bool) (weight : Fin k → Fin q),
          let code := fun e => ((weight e).val + q - 1) % q
          let active := fun i => (source i).elim true (Sum.elim
            (fun p => lit p.1 p.2.1 p.2.2)
            (fun p => !((code p.1).testBit p.2.val)))
          let Z := ((Finset.univ : Finset ((Fin m × Bool) → Bool)).filter (fun x =>
            (∀ p, ∀ r ∈ nb p, x p = true ∨ x r = true) ∧
            ∀ i, xor (x (i,false)) (x (i,true)) = active i)).card
          let factor := fun (y : Fin n → Bool) (e : Fin k) =>
            if ∀ i, lit e i (y i) = false then (weight e).val else 1
          0 < Z ∧ Z % q = (∑ y : Fin n → Bool, ∏ e : Fin k, factor y e) % q :=
  PEqualNP.Outside.L_lib_1210_aux.of_cons PEqualNP.Outside.L_lib_1210_aux.cons_ok
