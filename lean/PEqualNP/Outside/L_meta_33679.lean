import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan

namespace PEqualNP.Outside.L_meta_33679

open Finset

lemma f2_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · left; rfl
  · right; rfl

lemma f2_add_self (a : ZMod 2) : a + a = 0 := by
  rcases f2_cases a with rfl | rfl <;> decide

lemma symplectic_clique_free {P Q : Type} [Fintype P] [Fintype Q] [DecidableEq P]
    (μ ν : Q → P → ZMod 2) (S : Finset P)
    (hClique : ∀ p ∈ S, ∀ p' ∈ S, p ≠ p' →
      ∑ q : Q, (μ q p * ν q p' + ν q p * μ q p') = 1) :
    S.card ≤ 2 * Fintype.card Q + 1 := by
  classical
  by_contra hgt
  have hge : 2 * Fintype.card Q + 2 ≤ S.card := by omega
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq hge
  let W : P → P → ZMod 2 := fun p p' => ∑ q : Q, (μ q p * ν q p' + ν q p * μ q p')
  have hWdiag : ∀ p : P, W p p = 0 := by
    intro p
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [mul_comm (ν q p)]
    exact f2_add_self _
  let L : (T → ZMod 2) → (Q × Bool → ZMod 2) := fun z qb =>
    if qb.2 then ∑ p : T, ν qb.1 p.val * z p else ∑ p : T, μ qb.1 p.val * z p
  have hLinj : Function.Injective L := by
    intro z1 z2 hz
    set z : T → ZMod 2 := fun p => z1 p + z2 p
    have hdiff : ∀ qb, L z qb = 0 := by
      intro qb
      have h1 : L z1 qb = L z2 qb := congrFun hz qb
      cases hqb : qb.2
      · simp only [L, hqb, Bool.false_eq_true, ↓reduceIte, z] at h1 ⊢
        calc ∑ p : T, μ qb.1 p.val * (z1 p + z2 p)
            = ∑ p : T, (μ qb.1 p.val * z1 p + μ qb.1 p.val * z2 p) :=
                Finset.sum_congr rfl fun p _ => mul_add _ _ _
          _ = (∑ p : T, μ qb.1 p.val * z1 p) + (∑ p : T, μ qb.1 p.val * z2 p) :=
                Finset.sum_add_distrib
          _ = (∑ p : T, μ qb.1 p.val * z2 p) + (∑ p : T, μ qb.1 p.val * z2 p) := by rw [h1]
          _ = 0 := f2_add_self _
      · simp only [L, hqb, ↓reduceIte, z] at h1 ⊢
        calc ∑ p : T, ν qb.1 p.val * (z1 p + z2 p)
            = ∑ p : T, (ν qb.1 p.val * z1 p + ν qb.1 p.val * z2 p) :=
                Finset.sum_congr rfl fun p _ => mul_add _ _ _
          _ = (∑ p : T, ν qb.1 p.val * z1 p) + (∑ p : T, ν qb.1 p.val * z2 p) :=
                Finset.sum_add_distrib
          _ = (∑ p : T, ν qb.1 p.val * z2 p) + (∑ p : T, ν qb.1 p.val * z2 p) := by rw [h1]
          _ = 0 := f2_add_self _
    have hWz : ∀ p : T, ∑ p' : T, W p.val p'.val * z p' = 0 := by
      intro p
      calc ∑ p' : T, W p.val p'.val * z p'
          = ∑ p' : T, ∑ q : Q, (μ q p.val * (ν q p'.val * z p') + ν q p.val * (μ q p'.val * z p')) := by
              refine Finset.sum_congr rfl fun p' _ => ?_
              simp only [W, Finset.sum_mul]
              exact Finset.sum_congr rfl fun q _ => by ring
        _ = ∑ q : Q, ∑ p' : T, (μ q p.val * (ν q p'.val * z p') + ν q p.val * (μ q p'.val * z p')) :=
              Finset.sum_comm
        _ = ∑ q : Q, (μ q p.val * L z (q, true) + ν q p.val * L z (q, false)) := by
              refine Finset.sum_congr rfl fun q _ => ?_
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
              rfl
        _ = 0 := Finset.sum_eq_zero fun q _ => by rw [hdiff (q, true), hdiff (q, false)]; ring
    have hWz2 : ∀ p : T, (∑ p' : T, z p') + z p = 0 := by
      intro p
      have h0 := hWz p
      have hrew : ∑ p' : T, W p.val p'.val * z p' = ∑ p' : T, (z p' + (if p' = p then z p' else 0)) := by
        refine Finset.sum_congr rfl fun p' _ => ?_
        by_cases hpp : p' = p
        · subst hpp
          simp only [hWdiag, zero_mul, ↓reduceIte, f2_add_self]
        · have hne : p.val ≠ p'.val := fun heq => hpp (Subtype.ext heq.symm)
          have hW1 : W p.val p'.val = 1 := hClique p.val (hTS p.property) p'.val (hTS p'.property) hne
          simp only [hW1, one_mul, hpp, ↓reduceIte, add_zero]
      rw [hrew, Finset.sum_add_distrib] at h0
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at h0
      exact h0
    have hsum0 : ∑ p' : T, z p' = 0 := by
      have htot : ∑ p : T, ((∑ p' : T, z p') + z p) = 0 :=
        Finset.sum_eq_zero fun p _ => hWz2 p
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_coe, hTcard] at htot
      have heven : ((2 * Fintype.card Q + 2 : ℕ) : ZMod 2) = 0 := by
        have h2 : (2 : ZMod 2) = 0 := by decide
        push_cast
        rw [h2]
        ring
      rw [nsmul_eq_mul, heven, zero_mul, zero_add] at htot
      exact htot
    funext p
    have hp := hWz2 p
    rw [hsum0, zero_add] at hp
    have hzz : z p + z2 p = z2 p := by rw [hp, zero_add]
    simp only [z, add_assoc, f2_add_self, add_zero] at hzz
    exact hzz
  have hcard := Fintype.card_le_of_injective L hLinj
  have hLcard : Fintype.card (T → ZMod 2) = 2 ^ (2 * Fintype.card Q + 2) := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_coe, hTcard]
  have hRcard : Fintype.card (Q × Bool → ZMod 2) = 2 ^ (2 * Fintype.card Q) := by
    rw [Fintype.card_fun, ZMod.card, Fintype.card_prod, Fintype.card_bool, mul_comm]
  rw [hLcard, hRcard] at hcard
  have hle := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hcard
  omega

private def forwardEdges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Finset (Fin n × Fin n) :=
  univ.filter (fun p => p.1 < p.2 ∧ G.Adj p.1 p.2)

private theorem forwardEdges_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (forwardEdges G).card = G.edgeFinset.card := by
  let backwards := (univ : Finset (Fin n × Fin n)).filter
    (fun p => p.2 < p.1 ∧ G.Adj p.1 p.2)
  have hcard : backwards.card = (forwardEdges G).card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp
      have h := (Finset.mem_filter.mp hp).2
      exact Finset.mem_filter.mpr ⟨mem_univ _, h.1, h.2.symm⟩
    · intro a _ b _ eq
      exact Prod.ext (congrArg Prod.snd eq) (congrArg Prod.fst eq)
    · intro p hp
      have h := (Finset.mem_filter.mp hp).2
      exact ⟨(p.2, p.1), Finset.mem_filter.mpr ⟨mem_univ _, h.1, h.2.symm⟩, rfl⟩
  have hdisj : Disjoint (forwardEdges G) backwards := by
    rw [Finset.disjoint_left]
    intro p hp hq
    exact (lt_asymm (Finset.mem_filter.mp hp).2.1) (Finset.mem_filter.mp hq).2.1
  have hunion :
      (univ : Finset (Fin n × Fin n)).filter (fun p => G.Adj p.1 p.2) =
        forwardEdges G ∪ backwards := by
    ext p
    simp only [forwardEdges, backwards, mem_filter, mem_univ, true_and, mem_union]
    constructor
    · intro hadj
      rcases lt_or_gt_of_ne hadj.ne with hl | hg
      · exact Or.inl ⟨hl, hadj⟩
      · exact Or.inr ⟨hg, hadj⟩
    · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
  have h := G.two_mul_card_edgeFinset
  rw [hunion, card_union_of_disjoint hdisj, hcard] at h
  omega

theorem alternatingPairBound (s k : ℕ) (u v : Fin k → Fin s → ZMod 2) :
    ((univ : Finset (Fin s × Fin s)).filter (fun ij =>
      ij.1 < ij.2 ∧ (∑ j : Fin k, (u j ij.1 * v j ij.2 + v j ij.1 * u j ij.2)) = 1)).card ≤
    ((univ : Finset (Fin s × Fin s)).filter (fun ij =>
      ij.1 < ij.2 ∧ ij.1.val % (2*k+1) ≠ ij.2.val % (2*k+1))).card := by
  let W : Fin s → Fin s → ZMod 2 :=
    fun a b => ∑ j, (u j a * v j b + v j a * u j b)
  have hswap : ∀ a b, W a b = W b a := fun a b =>
    Finset.sum_congr rfl fun j _ => by ring
  have hdiag : ∀ a, W a a = 0 := fun a =>
    Finset.sum_eq_zero fun j _ => by
      rw [mul_comm (v j a)]
      exact f2_add_self _
  let G : SimpleGraph (Fin s) :=
    { Adj := fun a b => W a b = 1
      symm := ⟨fun a b ha => (hswap b a).trans ha⟩
      loopless := ⟨fun a ha => by rw [hdiag] at ha; exact zero_ne_one ha⟩ }
  letI : DecidableRel G.Adj := fun a b =>
    inferInstanceAs (Decidable (W a b = 1))
  have cf : G.CliqueFree (2*k+1+1) := by
    intro t ht
    have hb := symplectic_clique_free u v t ht.1
    rw [Fintype.card_fin, ht.2] at hb
    omega
  change (forwardEdges G).card ≤ (forwardEdges (SimpleGraph.turanGraph s (2*k+1))).card
  rw [forwardEdges_card, forwardEdges_card]
  exact (SimpleGraph.isTuranMaximal_turanGraph (n := s) (r := 2*k+1) (by omega)).2 cf

def HasRankLe {n m : ℕ} (M : Fin n → Fin m → ZMod 2) (r : ℕ) : Prop :=
  ∃ (u : Fin r → Fin n → ZMod 2) (v : Fin r → Fin m → ZMod 2), ∀ x y, M x y = ∑ i : Fin r, u i x * v i y

lemma hasRankLe_one {n m : ℕ} (a : Fin n → ZMod 2) (b : Fin m → ZMod 2) :
    HasRankLe (fun x y => a x * b y) 1 :=
  ⟨fun _ => a, fun _ => b, fun x y => by simp⟩

lemma hasRankLe_add {n m r1 r2 : ℕ} {M1 M2 : Fin n → Fin m → ZMod 2}
    (h1 : HasRankLe M1 r1) (h2 : HasRankLe M2 r2) :
    HasRankLe (fun x y => M1 x y + M2 x y) (r1 + r2) := by
  rcases h1 with ⟨u1, v1, hM1⟩
  rcases h2 with ⟨u2, v2, hM2⟩
  refine ⟨Fin.append u1 u2, Fin.append v1 v2, fun x y => ?_⟩
  dsimp only
  rw [Fin.sum_univ_add, hM1 x y, hM2 x y]
  simp [Fin.append_left, Fin.append_right]

lemma hasRankLe_sum {n m : ℕ} {ι : Type} (S : Finset ι) (f : ι → Fin n → ZMod 2) (g : ι → Fin m → ZMod 2) :
    HasRankLe (fun x y => ∑ i ∈ S, f i x * g i y) S.card := by
  classical
  let e : Fin S.card ≃ S := (Fintype.equivFinOfCardEq (Fintype.card_coe S)).symm
  refine ⟨fun i => f (e i).val, fun i => g (e i).val, fun x y => ?_⟩
  dsimp only
  rw [← Finset.sum_attach S]
  symm
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

lemma hasRankLe_sum_univ {n m : ℕ} {ι : Type} [Fintype ι] (f : ι → Fin n → ZMod 2) (g : ι → Fin m → ZMod 2) :
    HasRankLe (fun x y => ∑ i : ι, f i x * g i y) (Fintype.card ι) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨fun i => f (e i), fun i => g (e i), fun x y => ?_⟩
  dsimp only
  symm
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

private def anchor {n m : ℕ} (u : Fin n) (v : Fin m)
    (A : Matrix (Fin n) (Fin m) (ZMod 2)) : Matrix (Fin n) (Fin m) (ZMod 2) :=
  fun x y => A x y + A x v + A u y + A u v

private theorem rankLe_to_rank {n m r : ℕ} {A : Matrix (Fin n) (Fin m) (ZMod 2)}
    (h : HasRankLe A r) : A.rank ≤ r := by
  obtain ⟨u, v, hv⟩ := h
  let P : Matrix (Fin n) (Fin r) (ZMod 2) := fun x i => u i x
  let Q : Matrix (Fin r) (Fin m) (ZMod 2) := fun i y => v i y
  have eq : A = P * Q := by
    ext x y
    exact hv x y
  rw [eq]
  exact (Matrix.rank_mul_le_left P Q).trans (by simpa using Matrix.rank_le_card_width P)

private theorem hasRankLe_anchor {n m r : ℕ} {A : Matrix (Fin n) (Fin m) (ZMod 2)}
    (u : Fin n) (v : Fin m) (h : HasRankLe A r) : HasRankLe (anchor u v A) r := by
  obtain ⟨f, g, hfg⟩ := h
  refine ⟨fun i x => f i x + f i u, fun i y => g i y + g i v, fun x y => ?_⟩
  simp only [anchor, hfg, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

private theorem f2_mul_self (a : ZMod 2) : a * a = a := by
  rcases f2_cases a with rfl | rfl <;> decide

open scoped BigOperators

theorem anchoredRankOfTwoStageForm (n m s k : ℕ) (u : Fin n) (v : Fin m)
    (F : Matrix (Fin n) (Fin m) (ZMod 2))
    (pa pa' : Fin s → Fin n → ZMod 2) (pb pb' : Fin s → Fin m → ZMod 2)
    (Aout : Fin n → ZMod 2) (Bout : Fin m → ZMod 2) (cout : Fin s → ZMod 2)
    (lam : Fin k → ZMod 2)
    (Uq Uq' : Fin k → Fin n → ZMod 2) (Vq Vq' : Fin k → Fin m → ZMod 2)
    (μq νq : Fin k → Fin s → ZMod 2) (γq : Fin k → ZMod 2)
    (hShape : ∀ x y, F x y =
      Aout x + Bout y +
      (∑ p : Fin s, cout p * (pa p x * pb' p y + pa' p x * pb p y)) +
      ∑ q : Fin k, lam q *
        ((Uq q x + Vq q y + ∑ p : Fin s, μq q p * (pa p x * pb' p y + pa' p x * pb p y)) *
         (Uq' q x + Vq' q y + ∑ p : Fin s, νq q p * (pa p x * pb' p y + pa' p x * pb p y)) + γq q)) :
    (anchor u v F).rank ≤
      if k = 0 then 2*s else 2*k+4*s+4*
        ((univ : Finset (Fin s × Fin s)).filter
          (fun ij => ij.1 < ij.2 ∧ ij.1.val % (2*k+1) ≠ ij.2.val % (2*k+1))).card := by
  classical
  by_cases hk : k = 0
  · subst k
    simp only [ite_eq_left rfl, Finset.univ_eq_empty, Finset.sum_empty, add_zero] at hShape ⊢
    let T : Matrix (Fin n) (Fin m) (ZMod 2) :=
      fun x y => (∑ p : Fin s, cout p * pa p x * pb' p y) +
        ∑ p : Fin s, cout p * pa' p x * pb p y
    have hT : HasRankLe T (s+s) := by
      simpa only [Fintype.card_fin] using hasRankLe_add
        (hasRankLe_sum_univ (fun p x => cout p * pa p x) pb')
        (hasRankLe_sum_univ (fun p x => cout p * pa' p x) pb)
    have eq : anchor u v F = anchor u v T := by
      ext x y
      simp only [anchor, hShape, T]
      have hsplit : ∀ a b, (∑ p : Fin s, cout p * (pa p a * pb' p b + pa' p a * pb p b)) =
          (∑ p : Fin s, cout p * pa p a * pb' p b) +
          ∑ p : Fin s, cout p * pa' p a * pb p b := by
        intro a b
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun p _ => by ring
      simp only [hsplit]
      ring_nf
      simp only [show (2 : ZMod 2) = 0 by decide, mul_zero, zero_add, add_zero]
    rw [eq, two_mul]
    exact rankLe_to_rank (hasRankLe_anchor u v hT)
  rw [ite_eq_right hk]
  let P := Fin s
  let Q := Fin k
  let pVal : P → ℕ := Fin.val
  have hpInj : Function.Injective pVal := fun _ _ e => Fin.ext e
  let h : P → Fin n → Fin m → ZMod 2 := fun p x y => pa p x * pb' p y + pa' p x * pb p y
  let μ' : Q → P → ZMod 2 := fun q p => lam q * μq q p
  let ν' : Q → P → ZMod 2 := fun q p => lam q * νq q p
  let W : P → P → ZMod 2 := fun p p' => ∑ q : Q, (μ' q p * ν' q p' + ν' q p * μ' q p')
  have hWsymm : ∀ p p', W p p' = W p' p := fun p p' =>
    Finset.sum_congr rfl fun q _ => by ring
  let U : Finset (P × P) := (Finset.univ : Finset P) ×ˢ (Finset.univ : Finset P)
  let Eset : Finset (P × P) := U.filter (fun pp => pVal pp.1 < pVal pp.2 ∧ W pp.1 pp.2 = 1)
  let M0 : Fin n → Fin m → ZMod 2 := fun x y =>
    (Aout x + ∑ q : Q, lam q * (Uq q x * Uq' q x + γq q)) * 1 +
    1 * (Bout y + ∑ q : Q, lam q * (Vq q y * Vq' q y))
  let M1 : Fin n → Fin m → ZMod 2 := fun x y =>
    (∑ q : Q, (lam q * Uq q x) * Vq' q y) + (∑ q : Q, (lam q * Uq' q x) * Vq q y)
  let Xp : P → Fin n → ZMod 2 := fun p x =>
    cout p + ∑ q : Q, lam q * (μq q p * νq q p + Uq q x * νq q p + Uq' q x * μq q p)
  let Yp : P → Fin m → ZMod 2 := fun p y =>
    ∑ q : Q, lam q * (Vq q y * νq q p + Vq' q y * μq q p)
  let M2 : Fin n → Fin m → ZMod 2 := fun x y =>
    ((∑ p : P, (Xp p x * pa p x) * pb' p y) + (∑ p : P, (Xp p x * pa' p x) * pb p y)) +
    ((∑ p : P, pa p x * (Yp p y * pb' p y)) + (∑ p : P, pa' p x * (Yp p y * pb p y)))
  let M3 : Fin n → Fin m → ZMod 2 := fun x y =>
    ((∑ pp ∈ Eset, (pa pp.1 x * pa pp.2 x) * (pb' pp.1 y * pb' pp.2 y)) +
     (∑ pp ∈ Eset, (pa pp.1 x * pa' pp.2 x) * (pb' pp.1 y * pb pp.2 y))) +
    ((∑ pp ∈ Eset, (pa' pp.1 x * pa pp.2 x) * (pb pp.1 y * pb' pp.2 y)) +
     (∑ pp ∈ Eset, (pa' pp.1 x * pa' pp.2 x) * (pb pp.1 y * pb pp.2 y)))
  have hMsum : ∀ x y, F x y = ((M0 x y + M1 x y) + M2 x y) + M3 x y := by
    intro x y
    rw [hShape x y]
    have hQuad : ∑ q : Q, lam q * ((∑ p : P, μq q p * h p x y) * (∑ p' : P, νq q p' * h p' x y)) =
        (∑ p : P, (∑ q : Q, lam q * (μq q p * νq q p)) * h p x y) + M3 x y := by
      have h1 : ∑ q : Q, lam q * ((∑ p : P, μq q p * h p x y) * (∑ p' : P, νq q p' * h p' x y)) =
          ∑ p : P, ∑ p' : P, (∑ q : Q, lam q * (μq q p * νq q p')) * (h p x y * h p' x y) := by
        calc ∑ q : Q, lam q * ((∑ p : P, μq q p * h p x y) * (∑ p' : P, νq q p' * h p' x y))
            = ∑ q : Q, ∑ p : P, ∑ p' : P, lam q * (μq q p * νq q p') * (h p x y * h p' x y) := by
                refine Finset.sum_congr rfl fun q _ => ?_
                rw [Finset.sum_mul, Finset.mul_sum]
                refine Finset.sum_congr rfl fun p _ => ?_
                rw [Finset.mul_sum, Finset.mul_sum]
                exact Finset.sum_congr rfl fun p' _ => by ring
          _ = ∑ p : P, ∑ q : Q, ∑ p' : P, lam q * (μq q p * νq q p') * (h p x y * h p' x y) :=
                Finset.sum_comm
          _ = ∑ p : P, ∑ p' : P, ∑ q : Q, lam q * (μq q p * νq q p') * (h p x y * h p' x y) :=
                Finset.sum_congr rfl fun p _ => Finset.sum_comm
          _ = ∑ p : P, ∑ p' : P, (∑ q : Q, lam q * (μq q p * νq q p')) * (h p x y * h p' x y) :=
                Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ =>
                  (Finset.sum_mul _ _ _).symm
      rw [h1]
      let D : Finset (P × P) := U.filter (fun pp => pp.1 = pp.2)
      let LT : Finset (P × P) := U.filter (fun pp => pVal pp.1 < pVal pp.2)
      let GT : Finset (P × P) := U.filter (fun pp => pVal pp.2 < pVal pp.1)
      have hpart : U = D ∪ (LT ∪ GT) := by
        ext pp
        simp only [U, D, LT, GT, Finset.mem_union, Finset.mem_filter, Finset.mem_product,
          Finset.mem_univ, true_and]
        constructor
        · intro _
          rcases lt_trichotomy (pVal pp.1) (pVal pp.2) with hlt | heq | hgt
          · exact Or.inr (Or.inl hlt)
          · exact Or.inl (hpInj heq)
          · exact Or.inr (Or.inr hgt)
        · intro _; trivial
      have hd1 : Disjoint D (LT ∪ GT) := by
        rw [Finset.disjoint_left]
        intro pp hD hLG
        have heq := (Finset.mem_filter.mp hD).2
        rcases Finset.mem_union.mp hLG with hL | hG
        · have := (Finset.mem_filter.mp hL).2; rw [heq] at this; omega
        · have := (Finset.mem_filter.mp hG).2; rw [heq] at this; omega
      have hd2 : Disjoint LT GT := by
        rw [Finset.disjoint_left]
        intro pp hL hG
        have := (Finset.mem_filter.mp hL).2
        have := (Finset.mem_filter.mp hG).2
        omega
      have hsplit : ∑ p : P, ∑ p' : P, (∑ q : Q, lam q * (μq q p * νq q p')) * (h p x y * h p' x y) =
          (∑ p : P, (∑ q : Q, lam q * (μq q p * νq q p)) * h p x y) +
          ∑ pp ∈ LT, W pp.1 pp.2 * (h pp.1 x y * h pp.2 x y) := by
        have hprod : ∑ p : P, ∑ p' : P, (∑ q : Q, lam q * (μq q p * νq q p')) * (h p x y * h p' x y) =
            ∑ pp ∈ U, (∑ q : Q, lam q * (μq q pp.1 * νq q pp.2)) * (h pp.1 x y * h pp.2 x y) :=
          (Finset.sum_product' _ _ _).symm
        rw [hprod, hpart, Finset.sum_union hd1, Finset.sum_union hd2]
        congr 1
        · refine Finset.sum_bij (fun pp _ => pp.1) ?_ ?_ ?_ ?_
          · intro _ _; exact Finset.mem_univ _
          · intro pp1 h1 pp2 h2 heq
            have e1 := (Finset.mem_filter.mp h1).2
            have e2 := (Finset.mem_filter.mp h2).2
            exact Prod.ext heq (by rw [← e1, ← e2, heq])
          · intro p _
            exact ⟨(p, p), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, rfl⟩, rfl⟩
          · intro pp hpp
            have heq := (Finset.mem_filter.mp hpp).2
            rw [← heq, f2_mul_self]
        · have hGT : ∑ pp ∈ GT, (∑ q : Q, lam q * (μq q pp.1 * νq q pp.2)) * (h pp.1 x y * h pp.2 x y) =
              ∑ pp ∈ LT, (∑ q : Q, lam q * (μq q pp.2 * νq q pp.1)) * (h pp.1 x y * h pp.2 x y) := by
            refine Finset.sum_bij (fun pp _ => (pp.2, pp.1)) ?_ ?_ ?_ ?_
            · intro pp hpp
              exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
                (Finset.mem_filter.mp hpp).2⟩
            · intro pp1 _ pp2 _ heq; ext <;> simp_all
            · intro pp hpp
              exact ⟨(pp.2, pp.1), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
                (Finset.mem_filter.mp hpp).2⟩, by ext <;> rfl⟩
            · intro pp _
              simp only [mul_comm (h pp.1 x y)]
          rw [hGT, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun pp _ => ?_
          rw [← add_mul]
          congr 1
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun q _ => ?_
          simp only [μ', ν']
          have hlam2 : lam q * lam q = lam q := f2_mul_self (lam q)
          calc lam q * (μq q pp.1 * νq q pp.2) + lam q * (μq q pp.2 * νq q pp.1)
              = (lam q * lam q) * (μq q pp.1 * νq q pp.2) + (lam q * lam q) * (νq q pp.1 * μq q pp.2) := by
                  rw [hlam2]; ring
            _ = lam q * μq q pp.1 * (lam q * νq q pp.2) + lam q * νq q pp.1 * (lam q * μq q pp.2) := by ring
      rw [hsplit]
      congr 1
      have hfilt : ∑ pp ∈ LT, W pp.1 pp.2 * (h pp.1 x y * h pp.2 x y) = ∑ pp ∈ Eset, h pp.1 x y * h pp.2 x y := by
        have hsub : Eset = LT.filter (fun pp => W pp.1 pp.2 = 1) := by
          ext pp; simp [Eset, LT, and_assoc]
        symm
        rw [hsub, Finset.sum_filter]
        refine Finset.sum_congr rfl fun pp _ => ?_
        rcases f2_cases (W pp.1 pp.2) with h0 | h1
        · simp only [h0, zero_mul, show (0 : ZMod 2) ≠ 1 by decide, ↓reduceIte]
        · simp only [h1, one_mul, ↓reduceIte]
      rw [hfilt]
      simp only [M3, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun pp _ => ?_
      simp only [h]
      ring
    have hExpQ : ∑ q : Q, lam q * ((Uq q x + Vq q y + ∑ p : P, μq q p * h p x y) *
          (Uq' q x + Vq' q y + ∑ p : P, νq q p * h p x y) + γq q) =
        (∑ q : Q, lam q * (Uq q x * Uq' q x + γq q)) +
        (∑ q : Q, lam q * (Vq q y * Vq' q y)) +
        M1 x y +
        (∑ p : P, (∑ q : Q, lam q * (Uq q x * νq q p + Uq' q x * μq q p)) * h p x y) +
        (∑ p : P, (∑ q : Q, lam q * (Vq q y * νq q p + Vq' q y * μq q p)) * h p x y) +
        ∑ q : Q, lam q * ((∑ p : P, μq q p * h p x y) * (∑ p' : P, νq q p' * h p' x y)) := by
      have hlinX : ∑ p : P, (∑ q : Q, lam q * (Uq q x * νq q p + Uq' q x * μq q p)) * h p x y =
          ∑ q : Q, lam q * (Uq q x * (∑ p : P, νq q p * h p x y) + Uq' q x * (∑ p : P, μq q p * h p x y)) := by
        calc ∑ p : P, (∑ q : Q, lam q * (Uq q x * νq q p + Uq' q x * μq q p)) * h p x y
            = ∑ p : P, ∑ q : Q, lam q * (Uq q x * (νq q p * h p x y) + Uq' q x * (μq q p * h p x y)) := by
                refine Finset.sum_congr rfl fun p _ => ?_
                rw [Finset.sum_mul]
                exact Finset.sum_congr rfl fun q _ => by ring
          _ = ∑ q : Q, ∑ p : P, lam q * (Uq q x * (νq q p * h p x y) + Uq' q x * (μq q p * h p x y)) :=
                Finset.sum_comm
          _ = ∑ q : Q, lam q * (Uq q x * (∑ p : P, νq q p * h p x y) + Uq' q x * (∑ p : P, μq q p * h p x y)) := by
                refine Finset.sum_congr rfl fun q _ => ?_
                rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      have hlinY : ∑ p : P, (∑ q : Q, lam q * (Vq q y * νq q p + Vq' q y * μq q p)) * h p x y =
          ∑ q : Q, lam q * (Vq q y * (∑ p : P, νq q p * h p x y) + Vq' q y * (∑ p : P, μq q p * h p x y)) := by
        calc ∑ p : P, (∑ q : Q, lam q * (Vq q y * νq q p + Vq' q y * μq q p)) * h p x y
            = ∑ p : P, ∑ q : Q, lam q * (Vq q y * (νq q p * h p x y) + Vq' q y * (μq q p * h p x y)) := by
                refine Finset.sum_congr rfl fun p _ => ?_
                rw [Finset.sum_mul]
                exact Finset.sum_congr rfl fun q _ => by ring
          _ = ∑ q : Q, ∑ p : P, lam q * (Vq q y * (νq q p * h p x y) + Vq' q y * (μq q p * h p x y)) :=
                Finset.sum_comm
          _ = ∑ q : Q, lam q * (Vq q y * (∑ p : P, νq q p * h p x y) + Vq' q y * (∑ p : P, μq q p * h p x y)) := by
                refine Finset.sum_congr rfl fun q _ => ?_
                rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rw [hlinX, hlinY]
      simp only [M1, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ => by ring
    change _ = _
    rw [hExpQ, hQuad]
    have hM2eq : M2 x y = (∑ p : P, Xp p x * h p x y) + (∑ p : P, Yp p y * h p x y) := by
      simp only [M2, h, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => by ring
    have hXsum : ∑ p : P, Xp p x * h p x y =
        (∑ p : P, cout p * h p x y) +
        (∑ p : P, (∑ q : Q, lam q * (μq q p * νq q p)) * h p x y) +
        (∑ p : P, (∑ q : Q, lam q * (Uq q x * νq q p + Uq' q x * μq q p)) * h p x y) := by
      simp only [Xp, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      have : ∑ q : Q, lam q * (μq q p * νq q p + Uq q x * νq q p + Uq' q x * μq q p) =
          (∑ q : Q, lam q * (μq q p * νq q p)) +
          (∑ q : Q, lam q * (Uq q x * νq q p + Uq' q x * μq q p)) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun q _ => by ring
      rw [this]
      ring
    rw [hM2eq, hXsum]
    simp only [M0, Yp]
    ring
  have hR1 : HasRankLe M1 (2 * Fintype.card Q) := by
    have h1 := hasRankLe_add
      (hasRankLe_sum_univ (fun q x => lam q * Uq q x) (fun q y => Vq' q y))
      (hasRankLe_sum_univ (fun q x => lam q * Uq' q x) (fun q y => Vq q y))
    have heq : Fintype.card Q + Fintype.card Q = 2 * Fintype.card Q := by omega
    rw [heq] at h1
    exact h1
  have hR2 : HasRankLe M2 (4 * Fintype.card P) := by
    have ha := hasRankLe_add
      (hasRankLe_sum_univ (fun p x => Xp p x * pa p x) (fun p y => pb' p y))
      (hasRankLe_sum_univ (fun p x => Xp p x * pa' p x) (fun p y => pb p y))
    have hb := hasRankLe_add
      (hasRankLe_sum_univ (fun p x => pa p x) (fun p y => Yp p y * pb' p y))
      (hasRankLe_sum_univ (fun p x => pa' p x) (fun p y => Yp p y * pb p y))
    have hab := hasRankLe_add ha hb
    have h4 : Fintype.card P + Fintype.card P + (Fintype.card P + Fintype.card P) = 4 * Fintype.card P := by omega
    rw [h4] at hab
    exact hab
  have hR3 : HasRankLe M3 (4 * Eset.card) := by
    have ha := hasRankLe_add
      (hasRankLe_sum Eset (fun pp x => pa pp.1 x * pa pp.2 x) (fun pp y => pb' pp.1 y * pb' pp.2 y))
      (hasRankLe_sum Eset (fun pp x => pa pp.1 x * pa' pp.2 x) (fun pp y => pb' pp.1 y * pb pp.2 y))
    have hb := hasRankLe_add
      (hasRankLe_sum Eset (fun pp x => pa' pp.1 x * pa pp.2 x) (fun pp y => pb pp.1 y * pb' pp.2 y))
      (hasRankLe_sum Eset (fun pp x => pa' pp.1 x * pa' pp.2 x) (fun pp y => pb pp.1 y * pb pp.2 y))
    have hab := hasRankLe_add ha hb
    have h4 : Eset.card + Eset.card + (Eset.card + Eset.card) = 4 * Eset.card := by omega
    rw [h4] at hab
    exact hab
  let T : Matrix (Fin n) (Fin m) (ZMod 2) := fun x y => (M1 x y + M2 x y) + M3 x y
  have hT : HasRankLe T (2*k+4*s+4*Eset.card) := by
    have hb := hasRankLe_add (hasRankLe_add hR1 hR2) hR3
    simpa only [P, Q, Fintype.card_fin] using hb
  have eq : anchor u v F = anchor u v T := by
    ext x y
    simp only [anchor, hMsum, T, M0]
    ring_nf
    simp only [show (2 : ZMod 2) = 0 by decide, mul_zero, zero_add, add_zero]
  rw [eq]
  have hcard := alternatingPairBound s k μ' ν'
  have hEset : Eset = (univ : Finset (Fin s × Fin s)).filter
    (fun ij => ij.1 < ij.2 ∧ W ij.1 ij.2 = 1) := by
    ext ij
    simp only [Eset, U, pVal, P, Finset.univ_product_univ, Fin.val_fin_lt]
  have bound := rankLe_to_rank (hasRankLe_anchor u v hT)
  change (univ.filter (fun ij : Fin s × Fin s => ij.1 < ij.2 ∧ W ij.1 ij.2 = 1)).card ≤ _ at hcard
  rw [← hEset] at hcard
  exact bound.trans (by omega)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.Represents

def nonlinear (g : Gate) : Bool :=
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))

def depths (width : ℕ) (C : Circuit) : List ℕ :=
  C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)

def wiresStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def depthsStep (ds : List ℕ) (g : Gate) : List ℕ :=
  ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat]

lemma getD_append_left {α : Type} (l1 l2 : List α) (i : ℕ) (d : α) (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_right {α : Type} (l1 l2 : List α) (i : ℕ) (d : α) (hi : l1.length ≤ i) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right hi]

lemma getD_concat_last {α : Type} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  rw [getD_append_right l [a] l.length d (le_refl _)]
  simp

lemma wires_fold_length (gs : List Gate) (x : List Bool) :
    (gs.foldl wiresStep x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, wiresStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma depths_fold_length (gs : List Gate) (ds : List ℕ) :
    (gs.foldl depthsStep ds).length = ds.length + gs.length := by
  induction gs generalizing ds with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, depthsStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma wires_fold_getD_prefix (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (gs.foldl wiresStep x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have h1 : i < (wiresStep x g).length := by
      simp only [wiresStep, List.length_append, List.length_singleton]
      omega
    rw [ih (wiresStep x g) h1, wiresStep, getD_append_left x _ i false hi]

lemma depths_fold_getD_prefix (gs : List Gate) (ds : List ℕ) (i : ℕ) (hi : i < ds.length) :
    (gs.foldl depthsStep ds).getD i 0 = ds.getD i 0 := by
  induction gs generalizing ds with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have h1 : i < (depthsStep ds g).length := by
      simp only [depthsStep, List.length_append, List.length_singleton]
      omega
    rw [ih (depthsStep ds g) h1, depthsStep, getD_append_left ds _ i 0 hi]

lemma foldl_take_append_drop {α β : Type} (f : β → α → β) (init : β) (l : List α) (j : ℕ)
    (hj : j < l.length) :
    l.foldl f init = (l.drop (j + 1)).foldl f (f ((l.take j).foldl f init) l[j]) := by
  have hsplit : l = l.take j ++ [l[j]] ++ l.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j l]
    rw [List.append_assoc, List.cons_append, List.nil_append]
    congr 1
    exact (List.getElem_cons_drop hj).symm
  conv_lhs => rw [hsplit]
  rw [List.foldl_append, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl wiresStep x := rfl

lemma depths_eq_foldl (w : ℕ) (C : Circuit) :
    depths w C = C.gates.foldl depthsStep (List.replicate w 0) := rfl

lemma wires_getD_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  wires_fold_getD_prefix C.gates x i hi

lemma depths_getD_input (w : ℕ) (C : Circuit) (i : ℕ) (hi : i < w) :
    (depths w C).getD i 0 = 0 := by
  rw [depths_eq_foldl, depths_fold_getD_prefix]
  · simp [List.getD_eq_getElem?_getD, hi]
  · simp [hi]

lemma wires_getD_gate (w : ℕ) (C : Circuit) (hRB : ReadsBack w C) (x : List Bool)
    (hx : x.length = w) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (w + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => (C.wires x).getD i false) := by
  set pref := (C.gates.take j).foldl wiresStep x
  have hplen : pref.length = w + j := by
    rw [wires_fold_length, hx, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hfold : C.wires x = (C.gates.drop (j + 1)).foldl wiresStep (wiresStep pref C.gates[j]) := by
    rw [wires_eq_foldl, foldl_take_append_drop wiresStep x C.gates j hj]
  have hlt : w + j < (wiresStep pref C.gates[j]).length := by
    simp only [wiresStep, List.length_append, List.length_singleton, hplen]
    omega
  have hlhs : (C.wires x).getD (w + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i => pref.getD i false) := by
    rw [hfold, wires_fold_getD_prefix _ _ _ hlt, wiresStep, ← hplen, getD_concat_last]
  rw [hlhs, gateAt_eq_getElem C j hj]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi_lt : i < w + j := by
    have h1 := hRB j hj i
    rw [gateAt_eq_getElem C j hj] at h1
    exact h1 hi
  have hlt2 : i < (wiresStep pref C.gates[j]).length := by
    simp only [wiresStep, List.length_append, List.length_singleton, hplen]
    omega
  rw [hfold, wires_fold_getD_prefix _ _ _ hlt2, wiresStep, getD_append_left pref _ i false (by omega)]

lemma depths_getD_gate (w : ℕ) (C : Circuit) (hRB : ReadsBack w C) (j : ℕ) (hj : j < C.gates.length) :
    (depths w C).getD (w + j) 0 =
      ((gateAt C j).inputs.map fun i => (depths w C).getD i 0).foldr max 0 +
        (nonlinear (gateAt C j)).toNat := by
  set pref := (C.gates.take j).foldl depthsStep (List.replicate w 0)
  have hplen : pref.length = w + j := by
    rw [depths_fold_length, List.length_replicate, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hfold : depths w C = (C.gates.drop (j + 1)).foldl depthsStep (depthsStep pref C.gates[j]) := by
    rw [depths_eq_foldl, foldl_take_append_drop depthsStep (List.replicate w 0) C.gates j hj]
  have hlt : w + j < (depthsStep pref C.gates[j]).length := by
    simp only [depthsStep, List.length_append, List.length_singleton, hplen]
    omega
  have hlhs : (depths w C).getD (w + j) 0 =
      (C.gates[j].inputs.map fun i => pref.getD i 0).foldr max 0 + (nonlinear C.gates[j]).toNat := by
    rw [hfold, depths_fold_getD_prefix _ _ _ hlt, depthsStep, ← hplen, getD_concat_last]
  rw [hlhs, gateAt_eq_getElem C j hj]
  congr 1
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi_lt : i < w + j := by
    have h1 := hRB j hj i
    rw [gateAt_eq_getElem C j hj] at h1
    exact h1 hi
  have hlt2 : i < (depthsStep pref C.gates[j]).length := by
    simp only [depthsStep, List.length_append, List.length_singleton, hplen]
    omega
  rw [hfold, depths_fold_getD_prefix _ _ _ hlt2, depthsStep, getD_append_left pref _ i 0 (by omega)]

lemma foldr_max_le_iff (l : List ℕ) (k : ℕ) :
    l.foldr max 0 ≤ k ↔ ∀ a ∈ l, a ≤ k := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldr_cons, max_le_iff, List.mem_cons, forall_eq_or_imp, ih]

lemma getD_le_foldr_max (l : List ℕ) (w : ℕ) : l.getD w 0 ≤ l.foldr max 0 := by
  by_cases hlt : w < l.length
  · have hmem : l.getD w 0 ∈ l := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
      exact List.getElem_mem hlt
    exact (foldr_max_le_iff l _).mp (le_refl _) _ hmem
  · have hnone : l[w]? = none := List.getElem?_eq_none (by omega)
    simp only [List.getD_eq_getElem?_getD, hnone, Option.getD_none]
    exact Nat.zero_le _

def b2f (b : Bool) : ZMod 2 := if b then 1 else 0

lemma b2f_injective : Function.Injective b2f := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

lemma b2f_xor (a b : Bool) : b2f (xor a b) = b2f a + b2f b := by
  cases a <;> cases b <;> decide

lemma b2f_and (a b : Bool) : b2f (a && b) = b2f a * b2f b := by
  cases a <;> cases b <;> decide

lemma gate_eval_linear (g : Gate) (hFan : g.inputs.length ≤ 2) (hLin : nonlinear g = false) :
    (g.inputs = [] ∧ ∃ c : ZMod 2, b2f (g.op.eval []) = c) ∨
    (∃ a, g.inputs = [a] ∧ ∃ c0 c1 : ZMod 2, ∀ u : Bool,
      b2f (g.op.eval [u]) = c0 + c1 * b2f u) ∨
    (∃ a b, g.inputs = [a, b] ∧ ∃ c0 c1 c2 : ZMod 2, ∀ u v : Bool,
      b2f (g.op.eval [u, v]) = c0 + c1 * b2f u + c2 * b2f v) := by
  rcases h : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · left
    exact ⟨rfl, b2f (g.op.eval []), rfl⟩
  · right; left
    refine ⟨a, rfl, b2f (g.op.eval [false]), b2f (g.op.eval [true]) + b2f (g.op.eval [false]), ?_⟩
    intro u
    cases u <;> cases h0 : g.op.eval [false] <;> cases h1 : g.op.eval [true] <;> decide
  · right; right
    refine ⟨a, b, rfl, b2f (g.op.eval [false, false]),
      b2f (g.op.eval [true, false]) + b2f (g.op.eval [false, false]),
      b2f (g.op.eval [false, true]) + b2f (g.op.eval [false, false]), ?_⟩
    have hnl : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = false := by
      simp only [nonlinear, h, List.length_cons, List.length_nil, beq_self_eq_true,
        Bool.true_and] at hLin
      exact hLin
    intro u v
    cases h00 : g.op.eval [false, false] <;> cases h01 : g.op.eval [false, true] <;>
      cases h10 : g.op.eval [true, false] <;> cases h11 : g.op.eval [true, true] <;>
      simp only [h00, h01, h10, h11] at hnl <;>
      try (cases hnl) <;>
      cases u <;> cases v <;> simp only [h00, h01, h10, h11] <;> decide
  · simp [h] at hFan

lemma gate_eval_nonlinear (g : Gate) (hNL : nonlinear g = true) :
    ∃ a b, g.inputs = [a, b] ∧ ∃ α β γ : ZMod 2, ∀ u v : Bool,
      b2f (g.op.eval [u, v]) = (b2f u + β) * (b2f v + α) + γ := by
  have hlen : g.inputs.length = 2 := by
    simp only [nonlinear, Bool.and_eq_true, beq_iff_eq] at hNL
    exact hNL.1
  rcases h : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp [h] at hlen
  · simp [h] at hlen
  · have hnl : xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
        (xor (g.op.eval [true, false]) (g.op.eval [true, true])) = true := by
      simp only [nonlinear, h, List.length_cons, List.length_nil, beq_self_eq_true,
        Bool.true_and] at hNL
      exact hNL
    refine ⟨a, b, rfl,
      b2f (g.op.eval [true, false]) + b2f (g.op.eval [false, false]),
      b2f (g.op.eval [false, true]) + b2f (g.op.eval [false, false]),
      b2f (g.op.eval [false, false]) +
        (b2f (g.op.eval [false, true]) + b2f (g.op.eval [false, false])) *
        (b2f (g.op.eval [true, false]) + b2f (g.op.eval [false, false])), ?_⟩
    intro u v
    cases h00 : g.op.eval [false, false] <;> cases h01 : g.op.eval [false, true] <;>
      cases h10 : g.op.eval [true, false] <;> cases h11 : g.op.eval [true, true] <;>
      simp only [h00, h01, h10, h11] at hnl <;>
      try (cases hnl) <;>
      cases u <;> cases v <;> simp only [h00, h01, h10, h11] <;> decide
  · simp [h] at hlen

private theorem getD_le_of_all (ds : List ℕ) (hc : ∀ d ∈ ds, d ≤ 1) (i : ℕ) :
    ds.getD i 0 ≤ 1 := by
  by_cases hi : i < ds.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact hc _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    omega

private theorem splitDepthModel (w : ℕ) (C : Circuit) (cut : ℕ)
    (hcut : cut ≤ C.gates.length) (hRB : ReadsBack w C)
    (hL : ∀ d ∈ depths w ⟨C.gates.take cut, 0⟩, d ≤ 1)
    (hR : ∀ d ∈ depths (w+cut) ⟨C.gates.drop cut, 0⟩, d ≤ 1) :
    ∃ d : ℕ → ℕ, (∀ i < w, d i = 0) ∧ (∀ i, d i ≤ 2) ∧
      (∀ j < C.gates.length, nonlinear (gateAt C j) = false →
        ∀ i ∈ (gateAt C j).inputs, d i ≤ d (w+j)) ∧
      (∀ j < C.gates.length, nonlinear (gateAt C j) = true →
        if j < cut then d (w+j) = 1 ∧ ∀ i ∈ (gateAt C j).inputs, d i = 0
        else d (w+j) = 2 ∧ ∀ i ∈ (gateAt C j).inputs, d i ≤ 1) := by
  let L : Circuit := ⟨C.gates.take cut, 0⟩
  let R : Circuit := ⟨C.gates.drop cut, 0⟩
  have hLenL : L.gates.length = cut := by simp [L, Nat.min_eq_left hcut]
  have hLenR : R.gates.length = C.gates.length - cut := by simp [R]
  have hGateL (j : ℕ) (hj : j < cut) : gateAt L j = gateAt C j := by
    have hl : j < L.gates.length := by omega
    rw [gateAt_eq_getElem L j hl, gateAt_eq_getElem C j (by omega)]
    exact List.getElem_take
  have hGateR (j : ℕ) (hj : j < R.gates.length) : gateAt R j = gateAt C (cut+j) := by
    rw [gateAt_eq_getElem R j hj, gateAt_eq_getElem C (cut+j) (by omega)]
    exact List.getElem_drop
  have hReadL : ReadsBack w L := by
    intro j hj i hi
    have hjc : j < cut := by omega
    rw [hGateL j hjc] at hi
    exact hRB j (by omega) i hi
  have hReadR : ReadsBack (w+cut) R := by
    intro j hj i hi
    rw [hGateR j hj] at hi
    have h := hRB (cut+j) (by omega) i hi
    omega
  let l := fun i => (depths w L).getD i 0
  let r := fun i => (depths (w+cut) R).getD i 0
  let d := fun i => if i < w+cut then l i else r i + 1
  have capL : ∀ i, l i ≤ 1 := getD_le_of_all _ hL
  have capR : ∀ i, r i ≤ 1 := getD_le_of_all _ hR
  have haveL (j : ℕ) (hj : j < cut) :
      l (w+j) = ((gateAt C j).inputs.map l).foldr max 0 + (nonlinear (gateAt C j)).toNat := by
    have h := depths_getD_gate w L hReadL j (by omega)
    rw [hGateL j hj] at h
    exact h
  have haveR (j : ℕ) (hj : j < C.gates.length) (hjc : cut ≤ j) :
      r (w+j) = ((gateAt C j).inputs.map r).foldr max 0 + (nonlinear (gateAt C j)).toNat := by
    have hr : j-cut < R.gates.length := by omega
    have h := depths_getD_gate (w+cut) R hReadR (j-cut) hr
    rw [hGateR _ hr, show cut+(j-cut)=j by omega, show w+cut+(j-cut)=w+j by omega] at h
    exact h
  have dL (i : ℕ) (hi : i < w+cut) : d i = l i := by simp [d, hi]
  have dR (i : ℕ) (hi : w+cut ≤ i) : d i = r i + 1 := by simp [d, Nat.not_lt.mpr hi]
  refine ⟨d, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [dL i (by omega)]
    exact depths_getD_input w L i hi
  · intro i
    by_cases hi : i < w+cut
    · exact (dL i hi).trans_le (le_trans (capL i) (by decide))
    · rw [dR i (by omega)]
      have := capR i
      omega
  · intro j hj hlin i hi
    have hi' := hRB j hj i hi
    by_cases hjc : j < cut
    · rw [dL i (by omega), dL (w+j) (by omega), haveL j hjc]
      exact (foldr_max_le_iff _ _).mp (le_refl _) (l i) (List.mem_map_of_mem hi) |>.trans (Nat.le_add_right _ _)
    · rw [dR (w+j) (by omega)]
      by_cases hic : i < w+cut
      · rw [dL i hic]
        have := capL i
        omega
      · rw [dR i (by omega), haveR j hj (by omega)]
        have hlocal : r i ≤ ((gateAt C j).inputs.map r).foldr max 0 :=
          (foldr_max_le_iff _ _).mp (le_refl _) _ (List.mem_map_of_mem hi)
        omega
  · intro j hj hnl
    by_cases hjc : j < cut
    · simp only [ite_eq_left hjc]
      have hl := haveL j hjc
      rw [hnl] at hl
      change l (w+j) = _ + 1 at hl
      rw [dL (w+j) (by omega)]
      have hmax : ((gateAt C j).inputs.map l).foldr max 0 ≤ 0 := by
        have hcap := capL (w+j)
        omega
      constructor
      · omega
      · intro i hi
        have hi' := hRB j hj i hi
        rw [dL i (by omega)]
        have := (foldr_max_le_iff _ 0).mp hmax (l i) (List.mem_map_of_mem hi)
        omega
    · simp only [ite_eq_right hjc]
      have hr := haveR j hj (by omega)
      rw [hnl] at hr
      change r (w+j) = _ + 1 at hr
      rw [dR (w+j) (by omega)]
      have hmax : ((gateAt C j).inputs.map r).foldr max 0 ≤ 0 := by
        have hcap := capR (w+j)
        omega
      constructor
      · omega
      · intro i hi
        by_cases hic : i < w+cut
        · rw [dL i hic]; exact capL i
        · rw [dR i (by omega)]
          have := (foldr_max_le_iff _ 0).mp hmax (r i) (List.mem_map_of_mem hi)
          omega

lemma oneEach_length {n m : ℕ} (x : Fin n) (y : Fin m) :
    (oneEach x y).length = n + m := by
  simp [oneEach]

lemma oneEach_getD_left {n m : ℕ} (x : Fin n) (y : Fin m) (i : ℕ) (hi : i < n) :
    (oneEach x y).getD i false = decide (⟨i, hi⟩ = x) := by
  simp only [oneEach]
  rw [getD_append_left _ _ i false (by simp [hi])]
  simp [List.getD_eq_getElem?_getD, hi]

lemma oneEach_getD_right {n m : ℕ} (x : Fin n) (y : Fin m) (j : ℕ) (hj : j < m) :
    (oneEach x y).getD (n + j) false = decide (⟨j, hj⟩ = y) := by
  simp only [oneEach]
  rw [getD_append_right _ _ (n + j) false (by simp)]
  simp [List.getD_eq_getElem?_getD, hj]

private theorem countIndexed (l : List Gate) : ((Finset.range l.length).filter
          (fun j => nonlinear (l.getD j ⟨GateOp.or, []⟩) = true)).card =
          l.countP nonlinear := by
  rw [List.countP_eq_length_filter]
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton xs g ih =>
    rw [List.length_append, List.length_singleton, Finset.range_add_one,
      Finset.filter_insert, List.filter_append, List.length_append]
    have hprev : (Finset.range xs.length).filter
        (fun j => nonlinear ((xs ++ [g]).getD j ⟨GateOp.or, []⟩) = true) =
        (Finset.range xs.length).filter
        (fun j => nonlinear (xs.getD j ⟨GateOp.or, []⟩) = true) := by
      refine Finset.filter_congr fun j hj => ?_
      rw [getD_append_left xs [g] j _ (Finset.mem_range.mp hj)]
    rw [hprev, getD_concat_last]
    by_cases hg : nonlinear g = true
    · rw [ite_eq_left hg, Finset.card_insert_of_notMem (by simp), ih]
      simp [hg]
    · rw [ite_eq_right hg, ih]
      have hgf : nonlinear g = false := Bool.eq_false_iff.mpr hg
      simp [hgf]

private noncomputable def pad {T α : Type} [Fintype T] {r : ℕ} (f : T → α) (z : α) (i : Fin r) : α :=
  if h : i.val < Fintype.card T then f ((Fintype.equivFin T).symm ⟨i.val,h⟩) else z

private theorem paddedSum {T : Type} [Fintype T] {r : ℕ} (cap : Fintype.card T ≤ r)
    (f : T → ZMod 2) (g : Fin r → ZMod 2)
    (real : ∀ i (h : i.val < Fintype.card T), g i = f ((Fintype.equivFin T).symm ⟨i.val,h⟩))
    (extra : ∀ i, Fintype.card T ≤ i.val → g i = 0) :
    (∑ i, g i) = ∑ t, f t := by
  classical
  let keep := (univ : Finset (Fin r)).filter fun i => i.val < Fintype.card T
  have eq : (∑ i ∈ keep, g i) = ∑ i : Fin r, g i := by
    apply Finset.sum_subset (Finset.subset_univ keep)
    intro i _ hi
    apply extra
    exact Nat.le_of_not_gt (fun h => hi (mem_filter.mpr ⟨mem_univ _, h⟩))
  rw [← eq]
  let e : T → Fin r := fun t => Fin.castLE cap (Fintype.equivFin T t)
  symm
  refine Finset.sum_bij (fun t _ => e t) ?_ ?_ ?_ ?_
  · intro t _
    exact mem_filter.mpr ⟨mem_univ _, (Fintype.equivFin T t).isLt⟩
  · intro t _ t' _ he
    exact (Fintype.equivFin T).injective (Fin.ext (congrArg (fun i : Fin r => i.val) he))
  · intro i hi
    have h := (mem_filter.mp hi).2
    refine ⟨(Fintype.equivFin T).symm ⟨i.val,h⟩, mem_univ _, ?_⟩
    simp only [e, Equiv.apply_symm_apply]
    rfl
  · intro t _
    rw [real (e t) (Fintype.equivFin T t).isLt]
    simp [e]

private theorem circuitRankUpper (n m s k : ℕ) (u : Fin n) (v : Fin m)
    (G : Fin n → Fin m → Bool) (C : Circuit) (cut : ℕ)
    (hcut : cut ≤ C.gates.length) (hRB : ReadsBack (n+m) C)
    (hFan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hL : (C.gates.take cut).countP nonlinear ≤ s)
    (hR : (C.gates.drop cut).countP nonlinear ≤ k)
    (hDepthL : ∀ a ∈ depths (n+m) ⟨C.gates.take cut,0⟩, a ≤ 1)
    (hDepthR : ∀ a ∈ depths (n+m+cut) ⟨C.gates.drop cut,0⟩, a ≤ 1)
    (hRep : Represents G C) :
    (anchor u v (fun x y => b2f (G x y))).rank ≤
      if k = 0 then 2*s else 2*k+4*s+4*
        ((univ : Finset (Fin s × Fin s)).filter
          (fun ij => ij.1 < ij.2 ∧ ij.1.val % (2*k+1) ≠ ij.2.val % (2*k+1))).card := by
  classical
  let w := n + m
  let f : ℕ → Fin n → Fin m → ZMod 2 := fun wire x y =>
    b2f ((C.wires (oneEach x y)).getD wire false)
  obtain ⟨d, hInput, hDepth, hLinear, hNL⟩ := splitDepthModel w C cut hcut hRB hDepthL hDepthR
  by_cases ho : C.output < w+C.gates.length
  swap
  · have hZero (x : Fin n) (y : Fin m) : b2f (G x y) = 0 := by
      rw [← hRep x y]
      unfold Circuit.eval
      have hlen : (C.wires (oneEach x y)).length = w+C.gates.length := by
        rw [wires_eq_foldl, wires_fold_length, oneEach_length]
      rw [List.getD_eq_default _ _ (hlen ▸ Nat.le_of_not_gt ho)]
      rfl
    have hA : anchor u v (fun x y => b2f (G x y)) = 0 := by
      ext x y
      simp only [anchor, hZero, zero_add]
      rfl
    rw [hA, Matrix.rank_zero]
    exact Nat.zero_le _
  let P := (range C.gates.length).filter
    (fun j => nonlinear (gateAt C j) = true ∧ d (w+j) = 1)
  let Q := (range C.gates.length).filter
    (fun j => nonlinear (gateAt C j) = true ∧ d (w+j) = 2)
  have hDepth0 : ∀ wire < w + C.gates.length, d wire = 0 →
      ∃ (A : Fin n → ZMod 2) (B : Fin m → ZMod 2), ∀ x y, f wire x y = A x + B y := by
    intro wire
    induction wire using Nat.strong_induction_on with
    | ind wire ih =>
      intro hlt hd0
      by_cases hw : wire < w
      · by_cases hN1 : wire < n
        · refine ⟨fun x => b2f (decide (⟨wire, hN1⟩ = x)), fun _ => 0, fun x y => ?_⟩
          simp only [f, add_zero]
          rw [wires_getD_input C (oneEach x y) wire (by rw [oneEach_length]; exact hw)]
          rw [oneEach_getD_left x y wire hN1]
        · have hN2 : wire - n < m := by omega
          refine ⟨fun _ => 0, fun y => b2f (decide (⟨wire - n, hN2⟩ = y)), fun x y => ?_⟩
          simp only [f, zero_add]
          rw [wires_getD_input C (oneEach x y) wire (by rw [oneEach_length]; exact hw)]
          have heq : wire = n + (wire - n) := by omega
          have hr := oneEach_getD_right x y (wire - n) hN2
          rw [← heq] at hr
          rw [hr]
      · set j := wire - w
        have hj : j < C.gates.length := by omega
        have hwire : wire = w + j := by omega
        rw [hwire] at hd0 ⊢
        have hnl : nonlinear (gateAt C j) = false := by
          cases hn : nonlinear (gateAt C j)
          · rfl
          · have eq := hNL j hj hn
            split at eq <;> omega
        have hinp0 : ∀ a ∈ (gateAt C j).inputs, d a = 0 := by
          intro a ha
          have := hLinear j hj hnl a ha
          omega
        have hFan_j : (gateAt C j).inputs.length ≤ 2 := by
          rw [gateAt_eq_getElem C j hj]
          exact hFan _ (List.getElem_mem hj)
        rcases gate_eval_linear (gateAt C j) hFan_j hnl with
          ⟨h0, c, hc⟩ | ⟨a, h1, c0, c1, hc⟩ | ⟨a, b, h2, c0, c1, c2, hc⟩
        · refine ⟨fun _ => c, fun _ => 0, fun x y => ?_⟩
          simp only [f, add_zero]
          rw [wires_getD_gate w C hRB (oneEach x y) (oneEach_length x y) j hj, h0]
          exact hc
        · have ha_lt : a < w + j := hRB j hj a (by simp [h1])
          have ha0 : d a = 0 := hinp0 a (by simp [h1])
          obtain ⟨Aa, Ba, hfa⟩ := ih a (by omega) (by omega) ha0
          refine ⟨fun x => c0 + c1 * Aa x, fun y => c1 * Ba y, fun x y => ?_⟩
          simp only [f]
          rw [wires_getD_gate w C hRB (oneEach x y) (oneEach_length x y) j hj, h1]
          simp only [List.map_cons, List.map_nil]
          rw [hc]
          change c0 + c1 * f a x y = _
          rw [hfa x y]
          ring
        · have ha_lt : a < w + j := hRB j hj a (by simp [h2])
          have hb_lt : b < w + j := hRB j hj b (by simp [h2])
          obtain ⟨Aa, Ba, hfa⟩ := ih a (by omega) (by omega) (hinp0 a (by simp [h2]))
          obtain ⟨Ab, Bb, hfb⟩ := ih b (by omega) (by omega) (hinp0 b (by simp [h2]))
          refine ⟨fun x => c0 + c1 * Aa x + c2 * Ab x, fun y => c1 * Ba y + c2 * Bb y, fun x y => ?_⟩
          simp only [f]
          rw [wires_getD_gate w C hRB (oneEach x y) (oneEach_length x y) j hj, h2]
          simp only [List.map_cons, List.map_nil]
          rw [hc]
          change c0 + c1 * f a x y + c2 * f b x y = _
          rw [hfa x y, hfb x y]
          ring
  have hPrepSpec : ∀ p : P, ∃ (a a' : Fin n → ZMod 2) (b b' : Fin m → ZMod 2) (α : Fin n → ZMod 2) (β : Fin m → ZMod 2), ∀ x y,
      f (w + p.val) x y = a x * b' y + a' x * b y + α x + β y := by
    intro p
    have hp := Finset.mem_filter.mp p.property
    have hj : p.val < C.gates.length := Finset.mem_range.mp hp.1
    have hnl : nonlinear (gateAt C p.val) = true := hp.2.1
    have hd1 : d (w + p.val) = 1 := hp.2.2
    obtain ⟨u, v, huv, α0, β0, γ0, hgv⟩ := gate_eval_nonlinear (gateAt C p.val) hnl
    have hphase : p.val < cut := by
      by_contra hpLate
      have eq := hNL p.val hj hnl
      rw [ite_eq_right hpLate] at eq
      omega
    have hinputs := hNL p.val hj hnl
    rw [ite_eq_left hphase] at hinputs
    have hu_lt : u < w + p.val := hRB p.val hj u (by simp [huv])
    have hv_lt : v < w + p.val := hRB p.val hj v (by simp [huv])
    have hu0 : d u = 0 := hinputs.2 u (by simp [huv])
    have hv0 : d v = 0 := hinputs.2 v (by simp [huv])
    obtain ⟨Au, Bu, hfu⟩ := hDepth0 u (by omega) hu0
    obtain ⟨Av, Bv, hfv⟩ := hDepth0 v (by omega) hv0
    refine ⟨fun x => Au x + β0, fun x => Av x + α0, Bu, Bv,
      fun x => (Au x + β0) * (Av x + α0) + γ0, fun y => Bu y * Bv y, fun x y => ?_⟩
    simp only [f]
    rw [wires_getD_gate w C hRB (oneEach x y) (oneEach_length x y) p.val hj, huv]
    simp only [List.map_cons, List.map_nil]
    rw [hgv]
    change (f u x y + β0) * (f v x y + α0) + γ0 = _
    rw [hfu x y, hfv x y]
    ring
  choose pa pa' pb pb' pα pβ hpEq using hPrepSpec
  let h : P → Fin n → Fin m → ZMod 2 := fun p x y => pa p x * pb' p y + pa' p x * pb p y
  have hDepth1 : ∀ wire < w + C.gates.length, d wire ≤ 1 →
      ∃ (A : Fin n → ZMod 2) (B : Fin m → ZMod 2) (c : P → ZMod 2), ∀ x y,
        f wire x y = A x + B y + ∑ p : P, c p * h p x y := by
    intro wire
    induction wire using Nat.strong_induction_on with
    | ind wire ih =>
      intro hlt hd1
      by_cases hd0 : d wire = 0
      · obtain ⟨A, B, hAB⟩ := hDepth0 wire hlt hd0
        exact ⟨A, B, 0, fun x y => by simp [hAB x y]⟩
      · have hw : w ≤ wire := by
          by_contra hltw
          have := hInput wire (by omega)
          exact hd0 this
        set j := wire - w
        have hj : j < C.gates.length := by omega
        have hwire : wire = w + j := by omega
        rw [hwire] at hd1 hd0 ⊢
        by_cases hnl : nonlinear (gateAt C j) = true
        · have hjP : j ∈ P := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hnl, by omega⟩
          let pj : P := ⟨j, hjP⟩
          refine ⟨pα pj, pβ pj, fun p => if p = pj then 1 else 0, fun x y => ?_⟩
          rw [hpEq pj x y]
          simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, h]
          ring
        · have hnlf : nonlinear (gateAt C j) = false := Bool.eq_false_iff.mpr hnl
          have hinp1 : ∀ a ∈ (gateAt C j).inputs, d a ≤ 1 := by
            intro a ha
            have := hLinear j hj hnlf a ha
            omega
          have hFan_j : (gateAt C j).inputs.length ≤ 2 := by
            rw [gateAt_eq_getElem C j hj]
            exact hFan _ (List.getElem_mem hj)
          rcases gate_eval_linear (gateAt C j) hFan_j hnlf with
            ⟨h0, c, hc⟩ | ⟨a, h1, c0, c1, hc⟩ | ⟨a, b, h2, c0, c1, c2, hc⟩
          · refine ⟨fun _ => c, fun _ => 0, 0, fun x y => ?_⟩
            simp only [f, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
            rw [wires_getD_gate w C hRB (oneEach x y) (oneEach_length x y) j hj, h0]
            exact hc
          · have ha_lt : a < w + j := hRB j hj a (by simp [h1])
            obtain ⟨Aa, Ba, ca, hfa⟩ := ih a (by omega) (by omega) (hinp1 a (by simp [h1]))
            refine ⟨fun x => c0 + c1 * Aa x, fun y => c1 * Ba y, fun p => c1 * ca p, fun x y => ?_⟩
            simp only [f]
            rw [wires_getD_gate w C hRB (oneEach x y) (oneEach_length x y) j hj, h1]
            simp only [List.map_cons, List.map_nil]
            rw [hc]
            change c0 + c1 * f a x y = _
            rw [hfa x y, mul_add, mul_add, Finset.mul_sum]
            have hsm : ∑ p : P, c1 * (ca p * h p x y) = ∑ p : P, c1 * ca p * h p x y :=
              Finset.sum_congr rfl fun p _ => by ring
            rw [hsm]
            ring
          · have ha_lt : a < w + j := hRB j hj a (by simp [h2])
            have hb_lt : b < w + j := hRB j hj b (by simp [h2])
            obtain ⟨Aa, Ba, ca, hfa⟩ := ih a (by omega) (by omega) (hinp1 a (by simp [h2]))
            obtain ⟨Ab, Bb, cb, hfb⟩ := ih b (by omega) (by omega) (hinp1 b (by simp [h2]))
            refine ⟨fun x => c0 + c1 * Aa x + c2 * Ab x, fun y => c1 * Ba y + c2 * Bb y,
              fun p => c1 * ca p + c2 * cb p, fun x y => ?_⟩
            simp only [f]
            rw [wires_getD_gate w C hRB (oneEach x y) (oneEach_length x y) j hj, h2]
            simp only [List.map_cons, List.map_nil]
            rw [hc]
            change c0 + c1 * f a x y + c2 * f b x y = _
            rw [hfa x y, hfb x y]
            have hsm : ∑ p : P, (c1 * ca p + c2 * cb p) * h p x y =
                c1 * (∑ p : P, ca p * h p x y) + c2 * (∑ p : P, cb p * h p x y) := by
              rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl fun p _ => by ring
            rw [hsm]
            ring
  have hFinalSpec : ∀ q : Q, ∃ (Uq Uq' : Fin n → ZMod 2) (Vq Vq' : Fin m → ZMod 2) (μq νq : P → ZMod 2) (γq : ZMod 2),
      ∀ x y, f (w + q.val) x y =
        (Uq x + Vq y + ∑ p : P, μq p * h p x y) * (Uq' x + Vq' y + ∑ p : P, νq p * h p x y) + γq := by
    intro q
    have hq := Finset.mem_filter.mp q.property
    have hj : q.val < C.gates.length := Finset.mem_range.mp hq.1
    have hnl : nonlinear (gateAt C q.val) = true := hq.2.1
    have hd2 : d (w + q.val) = 2 := hq.2.2
    obtain ⟨u, v, huv, α0, β0, γ0, hgv⟩ := gate_eval_nonlinear (gateAt C q.val) hnl
    have hphase : ¬ q.val < cut := by
      intro hpEarly
      have eq := hNL q.val hj hnl
      rw [ite_eq_left hpEarly] at eq
      omega
    have hinputs := hNL q.val hj hnl
    rw [ite_eq_right hphase] at hinputs
    have hu_lt : u < w + q.val := hRB q.val hj u (by simp [huv])
    have hv_lt : v < w + q.val := hRB q.val hj v (by simp [huv])
    have hu1 : d u ≤ 1 := hinputs.2 u (by simp [huv])
    have hv1 : d v ≤ 1 := hinputs.2 v (by simp [huv])
    obtain ⟨Au, Bu, cu, hfu⟩ := hDepth1 u (by omega) hu1
    obtain ⟨Av, Bv, cv, hfv⟩ := hDepth1 v (by omega) hv1
    refine ⟨fun x => Au x + β0, fun x => Av x + α0, Bu, Bv, cu, cv, γ0, fun x y => ?_⟩
    simp only [f]
    rw [wires_getD_gate w C hRB (oneEach x y) (oneEach_length x y) q.val hj, huv]
    simp only [List.map_cons, List.map_nil]
    rw [hgv]
    change (f u x y + β0) * (f v x y + α0) + γ0 = _
    rw [hfu x y, hfv x y]
    ring
  choose Uq Uq' Vq Vq' μq νq γq hqEq using hFinalSpec
  have hDepth2 : ∀ wire < w + C.gates.length, d wire ≤ 2 →
      ∃ (A : Fin n → ZMod 2) (B : Fin m → ZMod 2) (c : P → ZMod 2) (lam : Q → ZMod 2), ∀ x y,
        f wire x y = A x + B y + ∑ p : P, c p * h p x y + ∑ q : Q, lam q * f (w + q.val) x y := by
    intro wire
    induction wire using Nat.strong_induction_on with
    | ind wire ih =>
      intro hlt hd2
      by_cases hd1 : d wire ≤ 1
      · obtain ⟨A, B, c, h1⟩ := hDepth1 wire hlt hd1
        exact ⟨A, B, c, 0, fun x y => by simp [h1 x y]⟩
      · have hw : w ≤ wire := by
          by_contra hltw
          have h0 : d wire = 0 := hInput wire (by omega)
          omega
        set j := wire - w
        have hj : j < C.gates.length := by omega
        have hwire : wire = w + j := by omega
        rw [hwire] at hd2 hd1 ⊢
        by_cases hnl : nonlinear (gateAt C j) = true
        · have hjQ : j ∈ Q := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hnl, by omega⟩
          let qj : Q := ⟨j, hjQ⟩
          refine ⟨0, 0, 0, fun q => if q = qj then 1 else 0, fun x y => ?_⟩
          simp [qj]
        · have hnlf : nonlinear (gateAt C j) = false := Bool.eq_false_iff.mpr hnl
          have hinp2 : ∀ a ∈ (gateAt C j).inputs, d a ≤ 2 := by
            intro a ha
            have := hLinear j hj hnlf a ha
            omega
          have hFan_j : (gateAt C j).inputs.length ≤ 2 := by
            rw [gateAt_eq_getElem C j hj]
            exact hFan _ (List.getElem_mem hj)
          rcases gate_eval_linear (gateAt C j) hFan_j hnlf with
            ⟨h0, c, hc⟩ | ⟨a, h1, c0, c1, hc⟩ | ⟨a, b, h2, c0, c1, c2, hc⟩
          · refine ⟨fun _ => c, fun _ => 0, 0, 0, fun x y => ?_⟩
            simp only [f, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]
            rw [wires_getD_gate w C hRB (oneEach x y) (oneEach_length x y) j hj, h0]
            exact hc
          · have ha_lt : a < w + j := hRB j hj a (by simp [h1])
            obtain ⟨Aa, Ba, ca, la, hfa⟩ := ih a (by omega) (by omega) (hinp2 a (by simp [h1]))
            refine ⟨fun x => c0 + c1 * Aa x, fun y => c1 * Ba y,
              fun p => c1 * ca p, fun q => c1 * la q, fun x y => ?_⟩
            simp only [f]
            rw [wires_getD_gate w C hRB (oneEach x y) (oneEach_length x y) j hj, h1]
            simp only [List.map_cons, List.map_nil]
            rw [hc]
            change c0 + c1 * f a x y = _
            rw [hfa x y]
            have h1s : ∑ p : P, c1 * ca p * h p x y = c1 * ∑ p : P, ca p * h p x y := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
            have h2s : ∑ q : Q, c1 * la q * f (w + q.val) x y = c1 * ∑ q : Q, la q * f (w + q.val) x y := by
              rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
            rw [h1s, h2s]
            ring
          · have ha_lt : a < w + j := hRB j hj a (by simp [h2])
            have hb_lt : b < w + j := hRB j hj b (by simp [h2])
            obtain ⟨Aa, Ba, ca, la, hfa⟩ := ih a (by omega) (by omega) (hinp2 a (by simp [h2]))
            obtain ⟨Ab, Bb, cb, lb, hfb⟩ := ih b (by omega) (by omega) (hinp2 b (by simp [h2]))
            refine ⟨fun x => c0 + c1 * Aa x + c2 * Ab x, fun y => c1 * Ba y + c2 * Bb y,
              fun p => c1 * ca p + c2 * cb p, fun q => c1 * la q + c2 * lb q, fun x y => ?_⟩
            simp only [f]
            rw [wires_getD_gate w C hRB (oneEach x y) (oneEach_length x y) j hj, h2]
            simp only [List.map_cons, List.map_nil]
            rw [hc]
            change c0 + c1 * f a x y + c2 * f b x y = _
            rw [hfa x y, hfb x y]
            have h1s : ∑ p : P, (c1 * ca p + c2 * cb p) * h p x y =
                c1 * (∑ p : P, ca p * h p x y) + c2 * (∑ p : P, cb p * h p x y) := by
              rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl fun _ _ => by ring
            have h2s : ∑ q : Q, (c1 * la q + c2 * lb q) * f (w + q.val) x y =
                c1 * (∑ q : Q, la q * f (w + q.val) x y) + c2 * (∑ q : Q, lb q * f (w + q.val) x y) := by
              rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
              exact Finset.sum_congr rfl fun _ _ => by ring
            rw [h1s, h2s]
            ring
  obtain ⟨Aout, Bout, cout, lam, hout⟩ := hDepth2 C.output ho (hDepth _)
  have hCardP : Fintype.card P ≤ s := by
    rw [Fintype.card_coe]
    let L := C.gates.take cut
    have hLen : L.length = cut := by simp [L, Nat.min_eq_left hcut]
    apply le_trans _ hL
    rw [← countIndexed L]
    apply Finset.card_le_card
    intro j hj
    obtain ⟨hj, hn, hd⟩ := mem_filter.mp hj
    have hle := mem_range.mp hj
    have hLeft : j < cut := by
      by_contra hbad
      have h := hNL j hle hn
      rw [ite_eq_right hbad] at h
      omega
    have hlt : j < L.length := by omega
    refine mem_filter.mpr ⟨mem_range.mpr hlt, ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    change nonlinear (C.gates.take cut)[j] = true
    rwa [List.getElem_take, ← gateAt_eq_getElem C j hle]
  have hCardQ : Fintype.card Q ≤ k := by
    rw [Fintype.card_coe]
    let R := C.gates.drop cut
    have hLen : R.length = C.gates.length-cut := by simp [R]
    have right (j : ℕ) (hj : j ∈ Q) : cut ≤ j := by
      obtain ⟨hj, hn, hd⟩ := mem_filter.mp hj
      by_contra! hbad
      have h := hNL j (mem_range.mp hj) hn
      rw [ite_eq_left hbad] at h
      omega
    apply le_trans _ hR
    rw [← countIndexed R]
    apply Finset.card_le_card_of_injOn (fun j => j-cut)
    · intro j hj
      have hre := right j hj
      obtain ⟨hj, hn, _⟩ := mem_filter.mp hj
      have hjc := mem_range.mp hj
      have hlt : j-cut < R.length := by omega
      refine mem_filter.mpr ⟨mem_range.mpr hlt, ?_⟩
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
      change nonlinear (C.gates.drop cut)[j-cut] = true
      rw [List.getElem_drop]
      have hidx : cut+(j-cut)=j := by omega
      simpa only [hidx, ← gateAt_eq_getElem] using hn
    · intro a ha b hb h
      change a - cut = b - cut at h
      have := right a ha
      have := right b hb
      omega
  let paS : Fin s → Fin n → ZMod 2 := pad pa 0
  let paS' : Fin s → Fin n → ZMod 2 := pad pa' 0
  let pbS : Fin s → Fin m → ZMod 2 := pad pb 0
  let pbS' : Fin s → Fin m → ZMod 2 := pad pb' 0
  let hS (p : Fin s) x y := paS p x * pbS' p y + paS' p x * pbS p y
  have prep (coeff : P → ZMod 2) (x : Fin n) (y : Fin m) :
      (∑ p : Fin s, pad coeff 0 p * hS p x y) = ∑ p : P, coeff p * h p x y := by
    apply paddedSum hCardP
    · intro i hi
      simp only [pad, hi, hS, paS, paS', pbS, pbS', h, ↓reduceDIte]
    · intro i hi
      simp only [pad, Nat.not_lt.mpr hi, ↓reduceDIte, zero_mul]
  let uqK : Fin k → Fin n → ZMod 2 := pad Uq 0
  let uqK' : Fin k → Fin n → ZMod 2 := pad Uq' 0
  let vqK : Fin k → Fin m → ZMod 2 := pad Vq 0
  let vqK' : Fin k → Fin m → ZMod 2 := pad Vq' 0
  let muK (q : Fin k) : Fin s → ZMod 2 := pad (pad μq 0 q) 0
  let nuK (q : Fin k) : Fin s → ZMod 2 := pad (pad νq 0 q) 0
  let gammaK : Fin k → ZMod 2 := pad γq 0
  let lambdaK : Fin k → ZMod 2 := pad lam 0
  refine anchoredRankOfTwoStageForm n m s k u v (fun x y => b2f (G x y))
    paS paS' pbS pbS' Aout Bout (pad cout 0) lambdaK uqK uqK' vqK vqK'
    muK nuK gammaK ?_
  intro x y
  have hg : b2f (G x y) = f C.output x y := by rw [← hRep x y]; rfl
  change _ = Aout x + Bout y + (∑ p : Fin s, pad cout 0 p * hS p x y) +
      ∑ q : Fin k, lambdaK q *
        ((uqK q x + vqK q y + ∑ p : Fin s, muK q p * hS p x y) *
         (uqK' q x + vqK' q y + ∑ p : Fin s, nuK q p * hS p x y) + gammaK q)
  rw [hg, hout, prep cout]
  congr 1
  symm
  apply paddedSum hCardQ
  · intro i hi
    let q := (Fintype.equivFin Q).symm ⟨i.val,hi⟩
    have hmu (p : Fin s) : muK i p = pad (μq q) 0 p := by simp only [muK, pad, hi, q, ↓reduceDIte]
    have hnu (p : Fin s) : nuK i p = pad (νq q) 0 p := by simp only [nuK, pad, hi, q, ↓reduceDIte]
    simp only [hmu, hnu, prep]
    simp only [lambdaK, uqK, vqK, uqK', vqK', gammaK, pad, hi, ↓reduceDIte]
    rw [hqEq]
  · intro i hi
    simp only [lambdaK, pad, Nat.not_lt.mpr hi, ↓reduceDIte, zero_mul]

private def turanPairs (s k : ℕ) : Finset (Fin s × Fin s) :=
  univ.filter (fun ij => ij.1 < ij.2 ∧ ij.1.val % (2*k+1) ≠ ij.2.val % (2*k+1))

private abbrev PairIndex (s k : ℕ) := ↥(turanPairs s k)

private abbrev Control (k : ℕ) := Fin k × Bool
private abbrev Base (s : ℕ) := Fin s × Bool
private abbrev Atom (s k : ℕ) := Control k ⊕ Base s
private abbrev Field := ZMod 2
private abbrev Assignment (s k : ℕ) := Atom s k → Field
private abbrev Feature (s k : ℕ) :=
  Control k ⊕ ((Base s × Bool) ⊕ (PairIndex s k × Bool × Bool))

private def feat {s k : ℕ} (lin : Fin s → Control k → Field) (shift : Fin s → Field)
    (x : Assignment s k) : Feature s k → Field
  | .inl c => x (.inl c)
  | .inr (.inl (b, false)) => x (.inr b)
  | .inr (.inl (b, true)) =>
      x (.inr b) * (shift b.1 + ∑ c : Control k, lin b.1 c * x (.inl c))
  | .inr (.inr (e, b, c)) => x (.inr (e.val.1,b)) * x (.inr (e.val.2,c))

private def indicator {s k : ℕ} (A : Finset (Atom s k)) : Assignment s k :=
  fun i => if i ∈ A then 1 else 0

private theorem pair_order {s k : ℕ} (e : PairIndex s k) : e.val.1 < e.val.2 :=
  (Finset.mem_filter.mp e.property).2.1

private theorem pair_probe {s k : ℕ} (lin : Fin s → Control k → Field) (shift : Fin s → Field)
    (e : PairIndex s k) (a b : Bool) (i : Feature s k) :
    let u : Atom s k := .inr (e.val.1,a)
    let v : Atom s k := .inr (e.val.2,b)
    feat lin shift (indicator {u,v}) i + feat lin shift (indicator {u}) i +
      feat lin shift (indicator {v}) i =
        if i = .inr (.inr (e,a,b)) then 1 else 0 := by
  have he := pair_order e
  have hne : (e.val.1,a) ≠ (e.val.2,b) :=
    fun eq => he.ne (congrArg (fun r : Base s => r.1) eq)
  rcases i with c | ⟨⟨p,t⟩, high⟩ | ⟨f,c,d⟩
  · simp [feat, indicator]
  · cases high <;>
      by_cases h1 : (p,t) = (e.val.1,a) <;>
      by_cases h2 : (p,t) = (e.val.2,b)
    all_goals try exact False.elim (hne (h1.symm.trans h2))
    all_goals
      simp only [feat, indicator, Finset.mem_insert, Finset.mem_singleton, Sum.inr.injEq,
        Sum.inl.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, h1, h2, hne, hne.symm, ↓reduceIte, true_or, or_true,
        false_or, or_false, mul_zero, one_mul, zero_mul, Finset.sum_const_zero,
        zero_add, add_zero, f2_add_self, reduceCtorEq]
  · have hf := pair_order f
    have hff : (f.val.1,c) ≠ (f.val.2,d) :=
      fun eq => hf.ne (congrArg (fun r : Base s => r.1) eq)
    have iff_eq : (f,c,d) = (e,a,b) ↔
        (f.val.1,c) = (e.val.1,a) ∧ (f.val.2,d) = (e.val.2,b) := by
      constructor
      · intro h
        have eq := Prod.mk.inj h
        rw [eq.1]
        exact ⟨Prod.ext rfl (Prod.mk.inj eq.2).1, Prod.ext rfl (Prod.mk.inj eq.2).2⟩
      · rintro ⟨h1,h2⟩
        have hfe : (f : Fin s × Fin s) = e.val :=
          Prod.ext (Prod.mk.inj h1).1 (Prod.mk.inj h2).1
        exact Prod.ext (Subtype.ext hfe) (Prod.ext (Prod.mk.inj h1).2 (Prod.mk.inj h2).2)
    have impossible (hc : (f.val.1,c) = (e.val.2,b))
        (hd : (f.val.2,d) = (e.val.1,a)) : False := by
      have h1 : f.val.1 = e.val.2 := (Prod.mk.inj hc).1
      have h2 : f.val.2 = e.val.1 := (Prod.mk.inj hd).1
      rw [h1,h2] at hf
      exact (lt_asymm he) hf
    by_cases ha : (f.val.1,c) = (e.val.1,a) <;>
    by_cases hb : (f.val.2,d) = (e.val.2,b) <;>
    by_cases hc : (f.val.1,c) = (e.val.2,b) <;>
    by_cases hd : (f.val.2,d) = (e.val.1,a)
    all_goals try exact False.elim (hff (ha.trans hd.symm))
    all_goals try exact False.elim (hff (hc.trans hb.symm))
    all_goals try exact False.elim (hne (ha.symm.trans hc))
    all_goals try exact False.elim (hne (hd.symm.trans hb))
    all_goals try exact False.elim (impossible hc hd)
    all_goals
      simp only [feat, indicator, mem_insert, mem_singleton, Sum.inr.injEq, iff_eq,
        ha, hb, hc, hd, hne, hne.symm, true_or, or_true, false_or, or_false, true_and, false_and,
        and_true, and_false, ↓reduceIte, one_mul, zero_mul, mul_zero, add_zero, zero_add]

private theorem mixed_probe {s k : ℕ} (lin : Fin s → Control k → Field) (shift : Fin s → Field)
    (b : Base s) (c : Control k) (hc : lin b.1 c = 1) (i : Feature s k) :
    let u : Atom s k := .inr b
    let v : Atom s k := .inl c
    feat lin shift (indicator {u,v}) i + feat lin shift (indicator {u}) i +
      feat lin shift (indicator {v}) i =
        if i = .inr (.inl (b,true)) then 1 else 0 := by
  rcases i with d | ⟨d,high⟩ | ⟨e,a,t⟩
  · by_cases eq : d = c <;> simp [feat, indicator, eq, f2_add_self]
  · cases high
    · by_cases eq : d = b <;> simp [feat, indicator, eq, f2_add_self]
    · have hsum : ∀ p : Fin s, (∑ t : Control k, lin p t *
            indicator ({Sum.inr b, Sum.inl c} : Finset (Atom s k)) (Sum.inl t)) = lin p c := by
        intro p
        simp [indicator, mul_ite, Finset.sum_ite_eq']
      by_cases eq : d = b
      · subst d
        simp only [feat, hsum, hc]
        simp [indicator]
        rw [add_comm (shift b.1) 1, add_assoc, f2_add_self, add_zero]
      · simp [feat, indicator, eq]
  · have hne := (pair_order e).ne
    by_cases eq : (e.val.1,a) = b <;> by_cases eq' : (e.val.2,t) = b
    · exact False.elim (hne (congrArg Prod.fst (eq.trans eq'.symm)))
    all_goals simp [feat, indicator, eq, eq']

private theorem features_injective {s k : ℕ} (lin : Fin s → Control k → Field) (shift : Fin s → Field)
    (hl : ∀ p, ∃ c, lin p c = 1)
    (z : Feature s k → Field)
    (hz : ∀ x, (∑ i, z i * feat lin shift x i) = 0) :
    z = 0 := by
  classical
  have one (t : Feature s k) : (∑ i, if i=t then z i else 0) = z t := by
    rw [Finset.sum_eq_single t]
    · simp
    · intro i _ hi; simp [hi]
    · simp
  have extract (a b : Atom s k) (t : Feature s k)
      (ht : ∀ i, feat lin shift (indicator {a,b}) i + feat lin shift (indicator {a}) i +
        feat lin shift (indicator {b}) i = if i=t then 1 else 0) : z t = 0 := by
    have hsum :
        ∑ i, z i * (feat lin shift (indicator {a,b}) i + feat lin shift (indicator {a}) i +
          feat lin shift (indicator {b}) i) = 0 := by
      simp only [mul_add, Finset.sum_add_distrib, hz, add_zero]
    exact (one t).symm.trans (by simpa only [ht, mul_ite, mul_one, mul_zero] using hsum)
  have allMixed : ∀ b : Base s, z (.inr (.inl (b,true))) = 0 := by
    intro b
    obtain ⟨c,hc⟩ := hl b.1
    exact extract (.inr b) (.inl c) _ (mixed_probe lin shift b c hc)
  funext i
  change z i = 0
  rcases i with c | ⟨b,high⟩ | ⟨e,a,b⟩
  · have h : ∀ i, feat lin shift (indicator {Sum.inl c}) i =
        if i = .inl c then 1 else 0 := by
      rintro (d | ⟨d, high⟩ | ⟨e,a,b⟩)
      · simp [feat,indicator]
      · cases high <;> simp [feat,indicator]
      · simp [feat,indicator]
    exact (one (.inl c)).symm.trans (by
      simpa only [h, mul_ite, mul_one, mul_zero] using hz (indicator {Sum.inl c}))
  · cases high
    · have h : ∀ i, z i * feat lin shift (indicator {Sum.inr b}) i =
          if i = .inr (.inl (b,false)) then z i else 0 := by
        rintro (c | ⟨c,high⟩ | ⟨e,a,d⟩)
        · simp [feat,indicator]
        · cases high
          · by_cases eq : c = b <;> simp [feat,indicator,eq]
          · simp [feat,indicator,allMixed]
        · have hne := (pair_order e).ne
          by_cases eq : (e.val.1,a) = b <;> by_cases eq' : (e.val.2,d) = b
          · exact False.elim (hne (congrArg Prod.fst (eq.trans eq'.symm)))
          all_goals simp [feat,indicator,eq,eq']
      exact (one (.inr (.inl (b,false)))).symm.trans (by simpa only [h] using hz (indicator {Sum.inr b}))
    · exact allMixed b
  · exact extract (.inr (e.val.1,a)) (.inr (e.val.2,b)) _ (pair_probe lin shift e a b)

def sympU (k : ℕ) (c : Fin (2 * k + 1)) (j : Fin k) : Bool :=
  decide (c.val / 2 = j.val)

def sympV (k : ℕ) (c : Fin (2 * k + 1)) (j : Fin k) : Bool :=
  decide (2 * j.val < c.val)

lemma symp_omega_lt (k : ℕ) (c1 c2 : Fin (2 * k + 1)) (hlt : c1.val < c2.val) :
    ∑ j : Fin k, (b2f (sympU k c1 j) * b2f (sympV k c2 j) +
      b2f (sympV k c1 j) * b2f (sympU k c2 j)) = 1 := by
  rw [Finset.sum_add_distrib]
  have hj1 : c1.val / 2 < k := by omega
  have h1 : ∑ j : Fin k, b2f (sympU k c1 j) * b2f (sympV k c2 j) = 1 := by
    have hterm : ∀ j : Fin k, b2f (sympU k c1 j) * b2f (sympV k c2 j) =
        if j = ⟨c1.val / 2, hj1⟩ then 1 else 0 := by
      intro j
      by_cases hj : j = ⟨c1.val / 2, hj1⟩
      · subst hj
        have h2 : 2 * (c1.val / 2) < c2.val := by omega
        simp [sympU, sympV, h2, b2f]
      · have hne : c1.val / 2 ≠ j.val := fun heq => hj (Fin.ext heq.symm)
        simp [sympU, hne, hj, b2f]
    simp [hterm]
  have h2 : ∑ j : Fin k, b2f (sympV k c1 j) * b2f (sympU k c2 j) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hju : c2.val / 2 = j.val
    · have hnot : ¬ (2 * j.val < c1.val) := by omega
      simp [sympV, hnot, b2f]
    · simp [sympU, hju, b2f]
  rw [h1, h2, add_zero]

lemma symp_omega_ne (k : ℕ) (c1 c2 : Fin (2 * k + 1)) (hne : c1 ≠ c2) :
    ∑ j : Fin k, (b2f (sympU k c1 j) * b2f (sympV k c2 j) +
      b2f (sympV k c1 j) * b2f (sympU k c2 j)) = 1 := by
  rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with hlt | hgt
  · exact symp_omega_lt k c1 c2 hlt
  · have := symp_omega_lt k c2 c1 hgt
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => by ring

def sympDiag (k : ℕ) (c : Fin (2 * k + 1)) : Bool :=
  decide (c.val % 2 = 1)

lemma symp_diag_eq (k : ℕ) (c : Fin (2 * k + 1)) :
    ∑ j : Fin k, b2f (sympU k c j) * b2f (sympV k c j) = b2f (sympDiag k c) := by
  by_cases hc : c.val < 2 * k
  · have hj0 : c.val / 2 < k := by omega
    have hterm : ∀ j : Fin k, b2f (sympU k c j) * b2f (sympV k c j) =
        if j = ⟨c.val / 2, hj0⟩ then b2f (sympDiag k c) else 0 := by
      intro j
      by_cases hj : j = ⟨c.val / 2, hj0⟩
      · subst hj
        have hiff : 2 * (c.val / 2) < c.val ↔ c.val % 2 = 1 := by omega
        simp [sympU, sympV, sympDiag, hiff, b2f]
      · have hne : c.val / 2 ≠ j.val := fun heq => hj (Fin.ext heq.symm)
        simp [sympU, hne, hj, b2f]
    simp [hterm]
  · have heq : c.val = 2 * k := by omega
    have hzero : ∀ j : Fin k, b2f (sympU k c j) * b2f (sympV k c j) = 0 := by
      intro j
      have hne : c.val / 2 ≠ j.val := by omega
      simp [sympU, hne, b2f]
    rw [Finset.sum_eq_zero fun j _ => hzero j]
    have hmod : c.val % 2 = 0 := by omega
    simp [sympDiag, hmod, b2f]

lemma symp_quad_sum_eq (s k : ℕ) (col : Fin s → Fin (2 * k + 1)) (Pval : Fin s → ZMod 2) :
    (∑ j : Fin k, (∑ p : Fin s, b2f (sympU k (col p) j) * Pval p) *
      (∑ p' : Fin s, b2f (sympV k (col p') j) * Pval p')) +
    (∑ p : Fin s, b2f (sympDiag k (col p)) * Pval p) =
    ∑ pp ∈ ((Finset.univ : Finset (Fin s)) ×ˢ (Finset.univ : Finset (Fin s))).filter (fun pp => pp.1.val < pp.2.val),
      (∑ j : Fin k, (b2f (sympU k (col pp.1) j) * b2f (sympV k (col pp.2) j) +
        b2f (sympV k (col pp.1) j) * b2f (sympU k (col pp.2) j))) * (Pval pp.1 * Pval pp.2) := by
  let U : Finset (Fin s × Fin s) := (Finset.univ : Finset (Fin s)) ×ˢ (Finset.univ : Finset (Fin s))
  let D : Finset (Fin s × Fin s) := U.filter (fun pp => pp.1 = pp.2)
  let LT : Finset (Fin s × Fin s) := U.filter (fun pp => pp.1.val < pp.2.val)
  let GT : Finset (Fin s × Fin s) := U.filter (fun pp => pp.2.val < pp.1.val)
  have h1 : ∑ j : Fin k, (∑ p : Fin s, b2f (sympU k (col p) j) * Pval p) *
      (∑ p' : Fin s, b2f (sympV k (col p') j) * Pval p') =
      ∑ pp ∈ U, (∑ j : Fin k, b2f (sympU k (col pp.1) j) * b2f (sympV k (col pp.2) j)) * (Pval pp.1 * Pval pp.2) := by
    dsimp only [U]
    rw [Finset.sum_product]
    calc ∑ j : Fin k, (∑ p : Fin s, b2f (sympU k (col p) j) * Pval p) *
          (∑ p' : Fin s, b2f (sympV k (col p') j) * Pval p')
        = ∑ j : Fin k, ∑ p : Fin s, ∑ p' : Fin s,
            b2f (sympU k (col p) j) * b2f (sympV k (col p') j) * (Pval p * Pval p') := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun p' _ => by ring
      _ = ∑ p : Fin s, ∑ j : Fin k, ∑ p' : Fin s,
            b2f (sympU k (col p) j) * b2f (sympV k (col p') j) * (Pval p * Pval p') := Finset.sum_comm
      _ = ∑ p : Fin s, ∑ p' : Fin s, ∑ j : Fin k,
            b2f (sympU k (col p) j) * b2f (sympV k (col p') j) * (Pval p * Pval p') :=
            Finset.sum_congr rfl fun p _ => Finset.sum_comm
      _ = ∑ p : Fin s, ∑ p' : Fin s,
            (∑ j : Fin k, b2f (sympU k (col p) j) * b2f (sympV k (col p') j)) * (Pval p * Pval p') :=
            Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => (Finset.sum_mul _ _ _).symm
  have hpart : U = D ∪ (LT ∪ GT) := by
    ext pp
    simp only [U, D, LT, GT, Finset.mem_union, Finset.mem_filter, Finset.mem_product,
      Finset.mem_univ, true_and]
    constructor
    · intro _
      rcases lt_trichotomy pp.1.val pp.2.val with hlt | heq | hgt
      · exact Or.inr (Or.inl hlt)
      · exact Or.inl (Fin.ext heq)
      · exact Or.inr (Or.inr hgt)
    · intro _; trivial
  have hd1 : Disjoint D (LT ∪ GT) := by
    rw [Finset.disjoint_left]
    intro pp hD hLG
    have heq := (Finset.mem_filter.mp hD).2
    rcases Finset.mem_union.mp hLG with hL | hG
    · have := (Finset.mem_filter.mp hL).2; rw [heq] at this; omega
    · have := (Finset.mem_filter.mp hG).2; rw [heq] at this; omega
  have hd2 : Disjoint LT GT := by
    rw [Finset.disjoint_left]
    intro pp hL hG
    have := (Finset.mem_filter.mp hL).2
    have := (Finset.mem_filter.mp hG).2
    omega
  have hDsum : ∑ pp ∈ D, (∑ j : Fin k, b2f (sympU k (col pp.1) j) * b2f (sympV k (col pp.2) j)) *
      (Pval pp.1 * Pval pp.2) = ∑ p : Fin s, b2f (sympDiag k (col p)) * Pval p := by
    refine Finset.sum_bij (fun pp _ => pp.1) ?_ ?_ ?_ ?_
    · intro _ _; exact Finset.mem_univ _
    · intro pp1 h1 pp2 h2 heq
      have e1 := (Finset.mem_filter.mp h1).2
      have e2 := (Finset.mem_filter.mp h2).2
      exact Prod.ext heq (by rw [← e1, ← e2, heq])
    · intro p _
      exact ⟨(p, p), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, rfl⟩, rfl⟩
    · intro pp hpp
      have heq := (Finset.mem_filter.mp hpp).2
      rw [← heq, f2_mul_self, symp_diag_eq]
  have hGTsum : ∑ pp ∈ GT, (∑ j : Fin k, b2f (sympU k (col pp.1) j) * b2f (sympV k (col pp.2) j)) *
      (Pval pp.1 * Pval pp.2) =
      ∑ pp ∈ LT, (∑ j : Fin k, b2f (sympV k (col pp.1) j) * b2f (sympU k (col pp.2) j)) *
      (Pval pp.1 * Pval pp.2) := by
    refine Finset.sum_bij (fun pp _ => (pp.2, pp.1)) ?_ ?_ ?_ ?_
    · intro pp hpp
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
        (Finset.mem_filter.mp hpp).2⟩
    · intro pp1 _ pp2 _ heq; ext <;> simp_all
    · intro pp hpp
      exact ⟨(pp.2, pp.1), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
        (Finset.mem_filter.mp hpp).2⟩, by ext <;> rfl⟩
    · intro pp _
      rw [mul_comm (Pval pp.1)]
      congr 1
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [h1, hpart, Finset.sum_union hd1, Finset.sum_union hd2, hDsum, hGTsum]
  set Sdiag := ∑ p : Fin s, b2f (sympDiag k (col p)) * Pval p
  set A := ∑ pp ∈ LT, (∑ j : Fin k, b2f (sympU k (col pp.1) j) * b2f (sympV k (col pp.2) j)) * (Pval pp.1 * Pval pp.2)
  set B := ∑ pp ∈ LT, (∑ j : Fin k, b2f (sympV k (col pp.1) j) * b2f (sympU k (col pp.2) j)) * (Pval pp.1 * Pval pp.2)
  have hcancel : Sdiag + (A + B) + Sdiag = A + B := by
    calc Sdiag + (A + B) + Sdiag = (Sdiag + Sdiag) + (A + B) := by ring
      _ = 0 + (A + B) := by rw [f2_add_self]
      _ = A + B := zero_add _
  rw [hcancel]
  simp only [A, B, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun pp _ => ?_
  rw [← add_mul, ← Finset.sum_add_distrib]

private theorem featureIndependent {s k : ℕ}
    (lin : Fin s → Control k → Field) (shift : Fin s → Field)
    (hl : ∀ p, ∃ c, lin p c = 1) :
    LinearIndependent Field (fun i : Feature s k => fun x : Assignment s k => feat lin shift x i) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro coeff h i
  have all := features_injective lin shift hl coeff (fun x => by
    have hx := congrFun h x
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using hx)
  exact congrFun all i

private def flipFeature {s k : ℕ} : Feature s k → Feature s k
  | .inl c => .inl c
  | .inr (.inl (b,h)) => .inr (.inl (b,!h))
  | .inr (.inr p) => .inr (.inr p)

private theorem flipFeature_involutive {s k : ℕ} :
    Function.Involutive (@flipFeature s k) := by
  rintro (c | ⟨b,h⟩ | p)
  · rfl
  · cases h <;> rfl
  · rfl

private def flipFeatureEquiv (s k : ℕ) : Feature s k ≃ Feature s k :=
  ⟨flipFeature, flipFeature, flipFeature_involutive, flipFeature_involutive⟩

private theorem featureRank (s k : ℕ)
    (la lb : Fin s → Control k → Field) (shift : Fin s → Field)
    (ha : ∀ p, ∃ c, la p c = 1) (hb : ∀ p, ∃ c, lb p c = 1) :
    Matrix.rank (m := Assignment s k) (n := Assignment s k)
      (fun x y => ∑ i : Feature s k, feat la 0 x i * feat lb shift y (flipFeature i)) =
        2*k+4*s+4*(turanPairs s k).card := by
  classical
  let L : Matrix (Assignment s k) (Feature s k) Field := fun x i => feat la 0 x i
  let R : Matrix (Feature s k) (Assignment s k) Field := fun i y => feat lb shift y (flipFeature i)
  have hL : L.rank = Fintype.card (Feature s k) := by
    rw [← Matrix.rank_transpose L]
    exact LinearIndependent.rank_matrix (featureIndependent la 0 ha)
  have hR : R.rank = Fintype.card (Feature s k) :=
    LinearIndependent.rank_matrix ((featureIndependent lb shift hb).comp _ flipFeature_involutive.injective)
  have bound : (L*R).rank = Fintype.card (Feature s k) := by
    have low := Matrix.rank_mul_ge L R
    have high := Matrix.rank_mul_le_left L R
    omega
  change (L*R).rank = _
  rw [bound]
  simp only [Feature, Control, Base, PairIndex, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_bool, Fintype.card_coe]
  omega

private def color (s k : ℕ) (i : Fin s) : Fin (2*k+1) :=
  ⟨i.val % (2*k+1), Nat.mod_lt _ (by omega)⟩

private def uCoeff {s k : ℕ} (i : Fin s) (j : Fin k) : Field :=
  b2f (sympU k (color s k i) j)

private def vCoeff {s k : ℕ} (i : Fin s) (j : Fin k) : Field :=
  b2f (sympV k (color s k i) j)

private def lc {s k : ℕ} (i : Fin s) (c : Control k) : Field :=
  if c.2 then uCoeff i c.1 else vCoeff i c.1

private def rc {s k : ℕ} (i : Fin s) (c : Control k) : Field :=
  if c.2 then vCoeff i c.1 else uCoeff i c.1

private def diagonal {s k : ℕ} (i : Fin s) : Field :=
  b2f (sympDiag k (color s k i))

private theorem u_or_v_nonzero {s k : ℕ} (hk : 0 < k) (i : Fin s) :
    (∃ j, uCoeff (k := k) i j = 1) ∨ ∃ j, vCoeff (k := k) i j = 1 := by
  let c := color s k i
  by_cases h : c.val < 2*k
  · left
    have hj : c.val / 2 < k := by omega
    exact ⟨⟨c.val/2,hj⟩, by simp [uCoeff, sympU, b2f, c]⟩
  · right
    have hc : c.val = 2*k := by have := c.isLt; omega
    refine ⟨⟨0,hk⟩, ?_⟩
    change b2f (sympV k c ⟨0,hk⟩) = 1
    have hpos : 0 < c.val := by omega
    simp [sympV, hpos, b2f]

private theorem lc_nonzero {s k : ℕ} (hk : 0 < k) (i : Fin s) :
    ∃ c : Control k, lc i c = 1 := by
  obtain ⟨j,hj⟩ | ⟨j,hj⟩ := u_or_v_nonzero hk i
  · exact ⟨(j,true), hj⟩
  · exact ⟨(j,false), hj⟩

private theorem rc_nonzero {s k : ℕ} (hk : 0 < k) (i : Fin s) :
    ∃ c : Control k, rc i c = 1 := by
  obtain ⟨j,hj⟩ | ⟨j,hj⟩ := u_or_v_nonzero hk i
  · exact ⟨(j,false), hj⟩
  · exact ⟨(j,true), hj⟩

private def prepValue {s k : ℕ} (x y : Assignment s k) (i : Fin s) : Field :=
  ∑ b : Bool, x (.inr (i,b)) * y (.inr (i,b))

private def twoStageValue {s k : ℕ} (x y : Assignment s k) : Field :=
  ∑ j : Fin k,
    (x (.inl (j,false)) + y (.inl (j,true)) + ∑ i : Fin s, uCoeff i j * prepValue x y i) *
    (x (.inl (j,true)) + y (.inl (j,false)) + ∑ i : Fin s, vCoeff i j * prepValue x y i)

private def controlValue {s k : ℕ} (l : Fin s → Control k → Field)
    (x : Assignment s k) (i : Fin s) : Field :=
  ∑ c : Control k, l i c * x (.inl c)

private def affineProducts {s k : ℕ} (x : Assignment s k) : Field :=
  ∑ j : Fin k, x (.inl (j,false)) * x (.inl (j,true))

private theorem pairSum {s k : ℕ} (p : Fin s → Field) :
    (∑ j : Fin k, (∑ i : Fin s, uCoeff i j * p i) * (∑ i : Fin s, vCoeff i j * p i)) =
      (∑ i : Fin s, diagonal (k := k) i * p i) +
        ∑ e : PairIndex s k, p e.val.1 * p e.val.2 := by
  classical
  have h := symp_quad_sum_eq s k (color s k) p
  change (∑ j : Fin k, (∑ i : Fin s, uCoeff i j * p i) * (∑ i : Fin s, vCoeff i j * p i)) +
      (∑ i : Fin s, diagonal (k := k) i * p i) =
    ∑ pp ∈ ((univ : Finset (Fin s)) ×ˢ (univ : Finset (Fin s))).filter
      (fun pp => pp.1.val < pp.2.val),
      (∑ j : Fin k, (uCoeff pp.1 j * vCoeff pp.2 j + vCoeff pp.1 j * uCoeff pp.2 j)) *
        (p pp.1 * p pp.2) at h
  have toFilter :
      (∑ e : PairIndex s k, p e.val.1 * p e.val.2) =
      ∑ e ∈ turanPairs s k, p e.1 * p e.2 := by
    rw [← Finset.sum_attach (turanPairs s k)]
    rfl
  have hr :
      (∑ pp ∈ ((univ : Finset (Fin s)) ×ˢ (univ : Finset (Fin s))).filter
        (fun pp => pp.1.val < pp.2.val),
        (∑ j : Fin k, (uCoeff pp.1 j * vCoeff pp.2 j + vCoeff pp.1 j * uCoeff pp.2 j)) *
          (p pp.1 * p pp.2)) =
      ∑ e ∈ turanPairs s k, p e.1 * p e.2 := by
    rw [Finset.univ_product_univ]
    have ht (ee : Fin s × Fin s) :
        (∑ j : Fin k, (uCoeff ee.1 j * vCoeff ee.2 j + vCoeff ee.1 j * uCoeff ee.2 j)) =
        if color s k ee.1 = color s k ee.2 then 0 else 1 := by
      by_cases hne : color s k ee.1 = color s k ee.2
      · rw [ite_eq_left hne]
        refine Finset.sum_eq_zero fun j _ => ?_
        simp only [uCoeff, vCoeff, hne]
        rw [mul_comm (b2f (sympV k (color s k ee.2) j)), f2_add_self]
      · rw [ite_eq_right hne]
        exact symp_omega_ne k (color s k ee.1) (color s k ee.2) hne
    simp only [ht, ite_mul, zero_mul, one_mul]
    simp only [turanPairs, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro e _
    have same : color s k e.1 = color s k e.2 ↔
        e.1.val % (2*k+1) = e.2.val % (2*k+1) := by
      constructor
      · exact fun eq => congrArg Fin.val eq
      · exact fun eq => Fin.ext eq
    change (if e.1.val < e.2.val then _ else 0) =
      (if e.1 < e.2 ∧ _ then _ else 0)
    have ltv : e.1.val < e.2.val ↔ e.1 < e.2 := Iff.rfl
    by_cases lt : e.1 < e.2
    · rw [ite_eq_left (ltv.mpr lt)]
      by_cases eq : e.1.val % (2*k+1) = e.2.val % (2*k+1)
      · have hcond : ¬(e.1 < e.2 ∧ e.1.val % (2*k+1) ≠ e.2.val % (2*k+1)) :=
          fun h => h.2 eq
        rw [ite_eq_left (same.mpr eq), ite_eq_right hcond]
      · have hcolor : color s k e.1 ≠ color s k e.2 := fun hc => eq (same.mp hc)
        rw [ite_eq_right hcolor, ite_eq_left (And.intro lt eq)]
    · rw [ite_eq_right (fun h => lt (ltv.mp h)), ite_eq_right (fun h => lt h.1)]
  rw [toFilter, ← hr]
  have hdiag := f2_add_self (∑ i : Fin s, diagonal (k := k) i * p i)
  rw [← h, add_comm (∑ i : Fin s, diagonal (k := k) i * p i), add_assoc, hdiag, add_zero]

private theorem stageCrossTerms {s k : ℕ} (x y : Assignment s k) :
    (∑ j : Fin k, ((x (.inl (j,false)) + y (.inl (j,true))) *
        (∑ i : Fin s, vCoeff i j * prepValue x y i) +
      (x (.inl (j,true)) + y (.inl (j,false))) *
        (∑ i : Fin s, uCoeff i j * prepValue x y i))) =
      ∑ i : Fin s, (controlValue lc x i + controlValue rc y i) * prepValue x y i := by
  classical
  calc
    _ = ∑ j : Fin k, ∑ i : Fin s,
        ((vCoeff i j * x (.inl (j,false)) + uCoeff i j * x (.inl (j,true))) +
         (uCoeff i j * y (.inl (j,false)) + vCoeff i j * y (.inl (j,true)))) *
          prepValue x y i := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_mul]
      simp only [controlValue, Control, Fintype.sum_prod_type, Fintype.sum_bool, lc, rc, Bool.false_eq_true, ↓reduceIte]
      rw [← Finset.sum_add_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring

private theorem featureDot {s k : ℕ} (x y : Assignment s k) :
    (∑ i : Feature s k, feat lc 0 x i * feat rc (diagonal (k := k)) y (flipFeature i)) =
      (∑ j : Fin k, (x (.inl (j,false)) * y (.inl (j,false)) +
        x (.inl (j,true)) * y (.inl (j,true)))) +
      (∑ i : Fin s, (controlValue lc x i + controlValue rc y i + diagonal (k := k) i) *
        prepValue x y i) +
      ∑ e : PairIndex s k, prepValue x y e.val.1 * prepValue x y e.val.2 := by
  classical
  simp only [Feature, Fintype.sum_sum_type]
  have hc :
      (∑ c : Control k, x (.inl c) * y (.inl c)) =
      ∑ j : Fin k, (x (.inl (j,false)) * y (.inl (j,false)) +
        x (.inl (j,true)) * y (.inl (j,true))) := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun j _ => by simp [Fintype.sum_bool, add_comm]
  have hm :
      (∑ f : Base s × Bool, feat lc 0 x (.inr (.inl f)) *
        feat rc (diagonal (k := k)) y (flipFeature (.inr (.inl f)))) =
      ∑ i : Fin s, (controlValue lc x i + controlValue rc y i + diagonal (k := k) i) *
        prepValue x y i := by
    simp only [Base, Fintype.sum_prod_type, Fintype.sum_bool, feat, flipFeature, Bool.not_true,
      Bool.not_false, Pi.zero_apply, zero_add, controlValue, prepValue]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hp :
      (∑ f : PairIndex s k × Bool × Bool, feat lc 0 x (.inr (.inr f)) *
        feat rc (diagonal (k := k)) y (flipFeature (.inr (.inr f)))) =
      ∑ e : PairIndex s k, prepValue x y e.val.1 * prepValue x y e.val.2 := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, feat, flipFeature, prepValue]
    exact Finset.sum_congr rfl fun e _ => by ring
  change (∑ c : Control k, x (.inl c) * y (.inl c)) +
    ((∑ f : Base s × Bool, feat lc 0 x (.inr (.inl f)) *
      feat rc (diagonal (k := k)) y (flipFeature (.inr (.inl f)))) +
     (∑ f : PairIndex s k × Bool × Bool, feat lc 0 x (.inr (.inr f)) *
      feat rc (diagonal (k := k)) y (flipFeature (.inr (.inr f))))) = _
  rw [hc, hm, hp]
  abel

private theorem polynomialFeatureExpansion {s k : ℕ} (x y : Assignment s k) :
    twoStageValue x y + twoStageValue x 0 + twoStageValue 0 y + twoStageValue (0 : Assignment s k) 0 =
    ∑ i : Feature s k, feat lc 0 x i * feat rc (diagonal (k := k)) y (flipFeature i) := by
  classical
  have lx : twoStageValue x (0 : Assignment s k) = affineProducts x := by
    simp [twoStageValue, prepValue, affineProducts]
  have ly : twoStageValue (0 : Assignment s k) y = affineProducts y := by
    simp [twoStageValue, prepValue, affineProducts, mul_comm]
  have lz : twoStageValue (0 : Assignment s k) 0 = 0 := by simp [twoStageValue, prepValue]
  rw [lx, ly, lz, add_zero, featureDot]
  have expand : twoStageValue x y + affineProducts x + affineProducts y =
      (∑ j : Fin k, (x (.inl (j,false)) * y (.inl (j,false)) +
        x (.inl (j,true)) * y (.inl (j,true)))) +
      (∑ j : Fin k, ((x (.inl (j,false)) + y (.inl (j,true))) *
        (∑ i : Fin s, vCoeff i j * prepValue x y i) +
      (x (.inl (j,true)) + y (.inl (j,false))) *
        (∑ i : Fin s, uCoeff i j * prepValue x y i))) +
      (∑ j : Fin k, (∑ i : Fin s, uCoeff i j * prepValue x y i) *
        (∑ i : Fin s, vCoeff i j * prepValue x y i)) := by
    simp only [twoStageValue, affineProducts, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    let xx := x (.inl (j,false)) * x (.inl (j,true))
    let yy := y (.inl (j,true)) * y (.inl (j,false))
    have he : xx + xx + yy + yy = 0 := by
      rw [f2_add_self, zero_add, f2_add_self]
    linear_combination he
  have merge :
      (∑ i : Fin s, (controlValue lc x i + controlValue rc y i)*prepValue x y i) +
        (∑ i : Fin s, diagonal (k:=k) i*prepValue x y i) =
        ∑ i : Fin s, (controlValue lc x i + controlValue rc y i+diagonal (k:=k) i)*prepValue x y i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [expand, stageCrossTerms, pairSum, ← merge]
  abel

structure Builder (width : ℕ) where
  gates : List Gate
  hRB : ∀ j < gates.length, ∀ i ∈ (gates.getD j ⟨GateOp.or, []⟩).inputs, i < width + j
  hFan : ∀ g ∈ gates, g.inputs.length ≤ 2

def Builder.empty (width : ℕ) : Builder width :=
  ⟨[], fun _ h => by simp at h, fun _ h => by simp at h⟩

def Builder.push {width : ℕ} (B : Builder width) (g : Gate)
    (hgRB : ∀ i ∈ g.inputs, i < width + B.gates.length) (hgFan : g.inputs.length ≤ 2) :
    Builder width × ℕ :=
  (⟨B.gates ++ [g], by
      intro j hj i hi
      rw [List.length_append, List.length_singleton] at hj
      by_cases hlt : j < B.gates.length
      · rw [getD_append_left B.gates [g] j _ hlt] at hi
        exact B.hRB j hlt i hi
      · have heq : j = B.gates.length := by omega
        subst heq
        rw [getD_concat_last] at hi
        exact hgRB i hi,
    by
      intro g' hg'
      rcases List.mem_append.mp hg' with h1 | h2
      · exact B.hFan g' h1
      · simp only [List.mem_singleton] at h2
        subst h2
        exact hgFan⟩,
   width + B.gates.length)

def Builder.wires {width : ℕ} (B : Builder width) (x : List Bool) : List Bool :=
  B.gates.foldl wiresStep x

def Builder.depths {width : ℕ} (B : Builder width) : List ℕ :=
  B.gates.foldl depthsStep (List.replicate width 0)

def Builder.nlCount {width : ℕ} (B : Builder width) : ℕ :=
  B.gates.countP nonlinear

lemma builder_push_wires_old {width : ℕ} (B : Builder width) (g : Gate)
    (hgRB : ∀ i ∈ g.inputs, i < width + B.gates.length) (hgFan : g.inputs.length ≤ 2)
    (x : List Bool) (hx : x.length = width) (w : ℕ) (hw : w < width + B.gates.length) :
    ((B.push g hgRB hgFan).1.wires x).getD w false = (B.wires x).getD w false := by
  simp only [Builder.push, Builder.wires, List.foldl_append, List.foldl_cons, List.foldl_nil, wiresStep]
  rw [getD_append_left]
  rw [wires_fold_length, hx]
  exact hw

lemma builder_push_wires_new {width : ℕ} (B : Builder width) (g : Gate)
    (hgRB : ∀ i ∈ g.inputs, i < width + B.gates.length) (hgFan : g.inputs.length ≤ 2)
    (x : List Bool) (hx : x.length = width) :
    ((B.push g hgRB hgFan).1.wires x).getD (B.push g hgRB hgFan).2 false =
      g.op.eval (g.inputs.map fun i => (B.wires x).getD i false) := by
  simp only [Builder.push, Builder.wires, List.foldl_append, List.foldl_cons, List.foldl_nil, wiresStep]
  have hlen : (B.gates.foldl wiresStep x).length = width + B.gates.length := by
    rw [wires_fold_length, hx]
  rw [← hlen, getD_concat_last]

lemma builder_push_depths_old {width : ℕ} (B : Builder width) (g : Gate)
    (hgRB : ∀ i ∈ g.inputs, i < width + B.gates.length) (hgFan : g.inputs.length ≤ 2)
    (w : ℕ) (hw : w < width + B.gates.length) :
    ((B.push g hgRB hgFan).1.depths).getD w 0 = (B.depths).getD w 0 := by
  simp only [Builder.push, Builder.depths, List.foldl_append, List.foldl_cons, List.foldl_nil, depthsStep]
  rw [getD_append_left]
  rw [depths_fold_length, List.length_replicate]
  exact hw

lemma builder_push_depths_new {width : ℕ} (B : Builder width) (g : Gate)
    (hgRB : ∀ i ∈ g.inputs, i < width + B.gates.length) (hgFan : g.inputs.length ≤ 2) :
    ((B.push g hgRB hgFan).1.depths).getD (B.push g hgRB hgFan).2 0 =
      (g.inputs.map fun i => (B.depths).getD i 0).foldr max 0 + (nonlinear g).toNat := by
  simp only [Builder.push, Builder.depths, List.foldl_append, List.foldl_cons, List.foldl_nil, depthsStep]
  have hlen : (B.gates.foldl depthsStep (List.replicate width 0)).length = width + B.gates.length := by
    rw [depths_fold_length, List.length_replicate]
  rw [← hlen, getD_concat_last]

lemma builder_push_nlCount {width : ℕ} (B : Builder width) (g : Gate)
    (hgRB : ∀ i ∈ g.inputs, i < width + B.gates.length) (hgFan : g.inputs.length ≤ 2) :
    (B.push g hgRB hgFan).1.nlCount = B.nlCount + (nonlinear g).toNat := by
  simp only [Builder.push, Builder.nlCount, List.countP_append, List.countP_singleton]
  cases nonlinear g <;> simp

lemma builder_push_len {width : ℕ} (B : Builder width) (g : Gate)
    (hgRB : ∀ i ∈ g.inputs, i < width + B.gates.length) (hgFan : g.inputs.length ≤ 2) :
    (B.push g hgRB hgFan).1.gates.length = B.gates.length + 1 := by
  simp [Builder.push]

lemma nonlinear_or_nil : nonlinear ⟨GateOp.or, []⟩ = false := rfl
lemma nonlinear_not (w : ℕ) : nonlinear ⟨GateOp.not, [w]⟩ = false := rfl
lemma nonlinear_mod2 (a b : ℕ) : nonlinear ⟨GateOp.mod 2, [a, b]⟩ = false := rfl
lemma nonlinear_and (a b : ℕ) : nonlinear ⟨GateOp.and, [a, b]⟩ = true := rfl

lemma eval_mod2_not (a b : Bool) :
    (!(GateOp.eval (GateOp.mod 2) [a, b])) = xor a b := by
  cases a <;> cases b <;> decide

def Builder.pushXor {width : ℕ} (B : Builder width) (a b : ℕ)
    (ha : a < width + B.gates.length) (hb : b < width + B.gates.length) :
    Builder width × ℕ :=
  let p1 := B.push ⟨GateOp.mod 2, [a, b]⟩
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi; rcases hi with rfl | rfl <;> assumption)
    (by simp)
  let p2 := p1.1.push ⟨GateOp.not, [p1.2]⟩
    (by intro i hi; simp only [List.mem_singleton] at hi; subst hi; simp [p1, Builder.push])
    (by simp)
  p2

lemma pushXor_len {width : ℕ} (B : Builder width) (a b : ℕ)
    (ha : a < width + B.gates.length) (hb : b < width + B.gates.length) :
    (B.pushXor a b ha hb).1.gates.length = B.gates.length + 2 := by
  simp [Builder.pushXor, Builder.push]

lemma pushXor_out_lt {width : ℕ} (B : Builder width) (a b : ℕ)
    (ha : a < width + B.gates.length) (hb : b < width + B.gates.length) :
    (B.pushXor a b ha hb).2 < width + (B.pushXor a b ha hb).1.gates.length := by
  simp [Builder.pushXor, Builder.push]

lemma pushXor_nlCount {width : ℕ} (B : Builder width) (a b : ℕ)
    (ha : a < width + B.gates.length) (hb : b < width + B.gates.length) :
    (B.pushXor a b ha hb).1.nlCount = B.nlCount := by
  simp only [Builder.pushXor, builder_push_nlCount, nonlinear_mod2, nonlinear_not]
  rfl

lemma pushXor_wires_old {width : ℕ} (B : Builder width) (a b : ℕ)
    (ha : a < width + B.gates.length) (hb : b < width + B.gates.length)
    (x : List Bool) (hx : x.length = width) (w : ℕ) (hw : w < width + B.gates.length) :
    ((B.pushXor a b ha hb).1.wires x).getD w false = (B.wires x).getD w false := by
  simp only [Builder.pushXor]
  rw [builder_push_wires_old _ _ _ _ x hx w (by simp [Builder.push]; omega)]
  rw [builder_push_wires_old _ _ _ _ x hx w hw]

lemma pushXor_wires_new {width : ℕ} (B : Builder width) (a b : ℕ)
    (ha : a < width + B.gates.length) (hb : b < width + B.gates.length)
    (x : List Bool) (hx : x.length = width) :
    ((B.pushXor a b ha hb).1.wires x).getD (B.pushXor a b ha hb).2 false =
      xor ((B.wires x).getD a false) ((B.wires x).getD b false) := by
  simp only [Builder.pushXor]
  rw [builder_push_wires_new _ _ _ _ x hx]
  simp only [List.map_cons, List.map_nil]
  rw [builder_push_wires_new _ _ _ _ x hx]
  simp only [List.map_cons, List.map_nil]
  have hnot : GateOp.eval GateOp.not [(GateOp.mod 2).eval [(B.wires x).getD a false, (B.wires x).getD b false]] =
      !((GateOp.mod 2).eval [(B.wires x).getD a false, (B.wires x).getD b false]) := rfl
  rw [hnot]
  exact eval_mod2_not _ _

lemma pushXor_depths_old {width : ℕ} (B : Builder width) (a b : ℕ)
    (ha : a < width + B.gates.length) (hb : b < width + B.gates.length)
    (w : ℕ) (hw : w < width + B.gates.length) :
    ((B.pushXor a b ha hb).1.depths).getD w 0 = (B.depths).getD w 0 := by
  simp only [Builder.pushXor]
  rw [builder_push_depths_old _ _ _ _ w (by simp [Builder.push]; omega)]
  rw [builder_push_depths_old _ _ _ _ w hw]

lemma pushXor_depths_new {width : ℕ} (B : Builder width) (a b : ℕ)
    (ha : a < width + B.gates.length) (hb : b < width + B.gates.length) :
    ((B.pushXor a b ha hb).1.depths).getD (B.pushXor a b ha hb).2 0 =
      max ((B.depths).getD a 0) ((B.depths).getD b 0) := by
  simp only [Builder.pushXor]
  rw [builder_push_depths_new]
  simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, nonlinear_not, Bool.toNat_false, add_zero]
  rw [builder_push_depths_new]
  simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, nonlinear_mod2, Bool.toNat_false, add_zero]
  omega

def Builder.foldXor {width : ℕ} (B : Builder width) (acc : ℕ) (hacc : acc < width + B.gates.length)
    (ws : List ℕ) (hws : ∀ w ∈ ws, w < width + B.gates.length) : Builder width × ℕ :=
  match ws with
  | [] => (B, acc)
  | w :: rest =>
    let p := B.pushXor acc w hacc (hws w (by simp))
    have hlen : B.gates.length ≤ p.1.gates.length := by rw [pushXor_len]; omega
    p.1.foldXor p.2 (pushXor_out_lt B acc w hacc _) rest
      (fun u hu => lt_of_lt_of_le (hws u (by simp [hu])) (Nat.add_le_add_left hlen width))

lemma foldXor_spec {width : ℕ} (B : Builder width) (acc : ℕ) (hacc : acc < width + B.gates.length)
    (ws : List ℕ) (hws : ∀ w ∈ ws, w < width + B.gates.length) (D : ℕ)
    (hdAcc : (B.depths).getD acc 0 ≤ D) (hdWs : ∀ w ∈ ws, (B.depths).getD w 0 ≤ D) :
    let res := B.foldXor acc hacc ws hws
    B.gates.length ≤ res.1.gates.length ∧
    res.2 < width + res.1.gates.length ∧
    res.1.nlCount = B.nlCount ∧
    (res.1.depths).getD res.2 0 ≤ D ∧
    (∀ w < width + B.gates.length, (res.1.depths).getD w 0 = (B.depths).getD w 0) ∧
    (∀ (x : List Bool), x.length = width →
      (∀ w < width + B.gates.length, (res.1.wires x).getD w false = (B.wires x).getD w false) ∧
      (res.1.wires x).getD res.2 false =
        ws.foldl (fun b w => xor b ((B.wires x).getD w false)) ((B.wires x).getD acc false)) := by
  induction ws generalizing B acc with
  | nil =>
    refine ⟨le_refl _, hacc, rfl, hdAcc, fun _ _ => rfl, fun x _ => ⟨fun _ _ => rfl, rfl⟩⟩
  | cons w rest ih =>
    simp only [Builder.foldXor]
    set p := B.pushXor acc w hacc (hws w (by simp))
    have hlen1 : B.gates.length ≤ p.1.gates.length := by rw [pushXor_len]; omega
    have hdP : (p.1.depths).getD p.2 0 ≤ D := by
      rw [pushXor_depths_new]
      exact max_le hdAcc (hdWs w (by simp))
    have hdRest : ∀ u ∈ rest, (p.1.depths).getD u 0 ≤ D := by
      intro u hu
      rw [pushXor_depths_old B acc w _ _ u (hws u (by simp [hu]))]
      exact hdWs u (by simp [hu])
    have hih := ih p.1 p.2 (pushXor_out_lt B acc w _ _)
      (fun u hu => lt_of_lt_of_le (hws u (by simp [hu])) (Nat.add_le_add_left hlen1 width))
      hdP hdRest
    rcases hih with ⟨hlen2, hout, hnl, hdOut, hdOld, hW⟩
    refine ⟨le_trans hlen1 hlen2, hout, by rw [hnl, pushXor_nlCount], hdOut, ?_, ?_⟩
    · intro u hu
      rw [hdOld u (by omega), pushXor_depths_old B acc w _ _ u hu]
    · intro x hx
      obtain ⟨hwOld, hwNew⟩ := hW x hx
      refine ⟨fun u hu => by rw [hwOld u (by omega), pushXor_wires_old B acc w _ _ x hx u hu], ?_⟩
      rw [hwNew, List.foldl_cons, pushXor_wires_new B acc w _ _ x hx]
      have hcongr : ∀ (b0 : Bool) (l : List ℕ), (∀ u ∈ l, u < width + B.gates.length) →
          l.foldl (fun b u => xor b ((p.1.wires x).getD u false)) b0 =
          l.foldl (fun b u => xor b ((B.wires x).getD u false)) b0 := by
        intro b0 l hl
        induction l generalizing b0 with
        | nil => rfl
        | cons u us ih2 =>
          simp only [List.foldl_cons]
          rw [pushXor_wires_old B acc w _ _ x hx u (hl u (by simp))]
          exact ih2 _ (fun v hv => hl v (by simp [hv]))
      exact hcongr _ rest (fun u hu => hws u (by simp [hu]))

def Builder.pushXorList {width : ℕ} (B : Builder width) (ws : List ℕ)
    (hws : ∀ w ∈ ws, w < width + B.gates.length) : Builder width × ℕ :=
  let p0 := B.push ⟨GateOp.or, []⟩ (by intro _ h; simp at h) (by simp)
  have hlen : B.gates.length ≤ p0.1.gates.length := by rw [builder_push_len]; omega
  p0.1.foldXor p0.2 (by simp [p0, Builder.push]) ws
    (fun u hu => lt_of_lt_of_le (hws u hu) (Nat.add_le_add_left hlen width))

lemma b2f_foldl_xor {α : Type} (l : List α) (f : α → Bool) (b0 : Bool) :
    b2f (l.foldl (fun b a => xor b (f a)) b0) = b2f b0 + (l.map fun a => b2f (f a)).sum := by
  induction l generalizing b0 with
  | nil => simp
  | cons a rest ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, b2f_xor, add_assoc]

lemma pushXorList_spec {width : ℕ} (B : Builder width) (ws : List ℕ)
    (hws : ∀ w ∈ ws, w < width + B.gates.length) (D : ℕ)
    (hdWs : ∀ w ∈ ws, (B.depths).getD w 0 ≤ D) :
    let res := B.pushXorList ws hws
    B.gates.length ≤ res.1.gates.length ∧
    res.2 < width + res.1.gates.length ∧
    res.1.nlCount = B.nlCount ∧
    (res.1.depths).getD res.2 0 ≤ D ∧
    (∀ w < width + B.gates.length, (res.1.depths).getD w 0 = (B.depths).getD w 0) ∧
    (∀ (x : List Bool), x.length = width →
      (∀ w < width + B.gates.length, (res.1.wires x).getD w false = (B.wires x).getD w false) ∧
      b2f ((res.1.wires x).getD res.2 false) = (ws.map fun w => b2f ((B.wires x).getD w false)).sum) := by
  simp only [Builder.pushXorList]
  set p0 := B.push ⟨GateOp.or, []⟩ (by intro _ h; simp at h) (by simp)
  have hlen0 : B.gates.length ≤ p0.1.gates.length := by rw [builder_push_len]; omega
  have hd0 : (p0.1.depths).getD p0.2 0 ≤ D := by
    rw [builder_push_depths_new]
    simp [nonlinear_or_nil]
  have hdWs' : ∀ w ∈ ws, (p0.1.depths).getD w 0 ≤ D := by
    intro w hw
    rw [builder_push_depths_old B _ _ _ w (hws w hw)]
    exact hdWs w hw
  have hspec := foldXor_spec p0.1 p0.2 (by simp [p0, Builder.push]) ws
    (fun u hu => lt_of_lt_of_le (hws u hu) (Nat.add_le_add_left hlen0 width)) D hd0 hdWs'
  rcases hspec with ⟨hlen1, hout, hnl, hdOut, hdOld, hW⟩
  refine ⟨le_trans hlen0 hlen1, hout, ?_, hdOut, ?_, ?_⟩
  · rw [hnl, builder_push_nlCount, nonlinear_or_nil]; rfl
  · intro w hw
    rw [hdOld w (by omega), builder_push_depths_old B _ _ _ w hw]
  · intro x hx
    obtain ⟨hwOld, hwNew⟩ := hW x hx
    refine ⟨fun w hw => by rw [hwOld w (by omega), builder_push_wires_old B _ _ _ x hx w hw], ?_⟩
    rw [hwNew, b2f_foldl_xor, builder_push_wires_new B _ _ _ x hx]
    simp only [List.map_nil, GateOp.eval, List.any_nil, b2f, Bool.false_eq_true, ↓reduceIte, zero_add]
    congr 1
    apply List.map_congr_left
    intro w hw
    rw [builder_push_wires_old B _ _ _ x hx w (hws w hw)]

private def DepthBound {width : ℕ} (B : Builder width) (d : ℕ) : Prop :=
  ∀ x ∈ B.depths, x ≤ d

private theorem depthBound_input {w D : ℕ} (B : Builder w) (h : DepthBound B D) (i : ℕ) :
    B.depths.getD i 0 ≤ D := by
  by_cases hi : i < B.depths.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Nat.zero_le _

private theorem pushDepthBound {w D T : ℕ} (B : Builder w) (g : Gate)
    (hRB : ∀ i ∈ g.inputs, i < w + B.gates.length) (hFan : g.inputs.length ≤ 2)
    (hB : DepthBound B D)
    (hin : ∀ i ∈ g.inputs, B.depths.getD i 0 ≤ T)
    (hout : T + (nonlinear g).toNat ≤ D) :
    DepthBound (B.push g hRB hFan).1 D := by
  intro d hd
  simp only [Builder.push, Builder.depths, List.foldl_append, List.foldl_cons,
    List.foldl_nil, depthsStep, List.mem_append, List.mem_singleton] at hd
  rcases hd with old | rfl
  · exact hB d old
  · have hmax : (g.inputs.map fun i => B.depths.getD i 0).foldr max 0 ≤ T := by
      apply (foldr_max_le_iff _ _).mpr
      intro a ha
      obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
      exact hin i hi
    exact (Nat.add_le_add_right hmax _).trans hout

private theorem pushAffineBound {w D : ℕ} (B : Builder w) (g : Gate)
    (hRB : ∀ i ∈ g.inputs, i < w + B.gates.length) (hFan : g.inputs.length ≤ 2)
    (hlin : nonlinear g = false) (hB : DepthBound B D) :
    DepthBound (B.push g hRB hFan).1 D :=
  pushDepthBound B g hRB hFan hB (fun i _ => depthBound_input B hB i) (by simp [hlin])

private theorem pushXorBound {w D : ℕ} (B : Builder w) (a b : ℕ)
    (ha : a < w+B.gates.length) (hb : b < w+B.gates.length) (hB : DepthBound B D) :
    DepthBound (B.pushXor a b ha hb).1 D := by
  unfold Builder.pushXor
  apply pushAffineBound _ _ _ _ (nonlinear_not _)
  exact pushAffineBound _ _ _ _ (nonlinear_mod2 _ _) hB

private theorem foldXorBound {w D : ℕ} (B : Builder w) (a : ℕ)
    (ha : a < w+B.gates.length) (ws : List ℕ)
    (hws : ∀ i ∈ ws, i < w+B.gates.length) (hB : DepthBound B D) :
    DepthBound (B.foldXor a ha ws hws).1 D := by
  induction ws generalizing B a with
  | nil => exact hB
  | cons b rest ih =>
    simp only [Builder.foldXor]
    apply ih
    exact pushXorBound _ _ _ _ _ hB

private theorem pushXorListBound {w D : ℕ} (B : Builder w) (ws : List ℕ)
    (hws : ∀ i ∈ ws, i < w+B.gates.length) (hB : DepthBound B D) :
    DepthBound (B.pushXorList ws hws).1 D := by
  unfold Builder.pushXorList
  apply foldXorBound
  exact pushAffineBound _ _ _ _ nonlinear_or_nil hB

def pushManyXor {width : ℕ} (B : Builder width) (n : ℕ)
    (ws : Fin n → List ℕ) (hws : ∀ i w, w ∈ ws i → w < width + B.gates.length) :
    { p : Builder width × (Fin n → ℕ) //
      B.gates.length ≤ p.1.gates.length ∧
      (∀ i, p.2 i < width + p.1.gates.length) ∧
      p.1.nlCount = B.nlCount ∧
      (∀ D, (∀ i w, w ∈ ws i → (B.depths).getD w 0 ≤ D) → ∀ i, (p.1.depths).getD (p.2 i) 0 ≤ D) ∧
      (∀ w < width + B.gates.length, (p.1.depths).getD w 0 = (B.depths).getD w 0) ∧
      (∀ x : List Bool, x.length = width →
        (∀ w < width + B.gates.length, (p.1.wires x).getD w false = (B.wires x).getD w false) ∧
        ∀ i, b2f ((p.1.wires x).getD (p.2 i) false) = (ws i |>.map fun w => b2f ((B.wires x).getD w false)).sum) ∧
      (∀ D, DepthBound B D → DepthBound p.1 D) } := by
  induction n generalizing B with
  | zero =>
    exact ⟨(B, Fin.elim0), le_refl _, fun i => i.elim0, rfl, fun _ _ i => i.elim0,
      fun _ _ => rfl, ⟨fun _ _ => ⟨fun _ _ => rfl, fun i => i.elim0⟩, fun _ h => h⟩⟩
  | succ n ih =>
    let p1 := B.pushXorList (ws 0) (hws 0)
    have hbase := pushXorList_spec B (ws 0) (hws 0) (B.depths.foldr max 0) (fun w _ => getD_le_foldr_max B.depths w)
    have hlen1 : B.gates.length ≤ p1.1.gates.length := hbase.1
    let ws' : Fin n → List ℕ := fun i => ws i.succ
    have hws' : ∀ i w, w ∈ ws' i → w < width + p1.1.gates.length := fun i w hw =>
      lt_of_lt_of_le (hws i.succ w hw) (Nat.add_le_add_left hlen1 width)
    let r2 := ih p1.1 ws' hws'
    refine ⟨(r2.val.1, Fin.cons p1.2 r2.val.2), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact le_trans hlen1 r2.property.1
    · intro i
      refine Fin.cases ?_ ?_ i
      · simp only [Fin.cons_zero]
        have h1 : p1.2 < width + p1.1.gates.length := hbase.2.1
        have h2 : p1.1.gates.length ≤ r2.val.1.gates.length := r2.property.1
        omega
      · intro j; simp only [Fin.cons_succ]; exact r2.property.2.1 j
    · rw [r2.property.2.2.1, hbase.2.2.1]
    · intro D hD i
      have hs1 := pushXorList_spec B (ws 0) (hws 0) D (hD 0)
      refine Fin.cases ?_ ?_ i
      · simp only [Fin.cons_zero]
        rw [r2.property.2.2.2.2.1 p1.2 hs1.2.1]
        exact hs1.2.2.2.1
      · intro j
        simp only [Fin.cons_succ]
        refine r2.property.2.2.2.1 D ?_ j
        intro k w hw
        rw [hs1.2.2.2.2.1 w (hws k.succ w hw)]
        exact hD k.succ w hw
    · intro w hw
      rw [r2.property.2.2.2.2.1 w (by omega), hbase.2.2.2.2.1 w hw]
    · constructor
      · intro x hx
        obtain ⟨hwOld1, hwNew1⟩ := hbase.2.2.2.2.2 x hx
        obtain ⟨hwOld2, hwNew2⟩ := r2.property.2.2.2.2.2.1 x hx
        refine ⟨fun w hw => by rw [hwOld2 w (by omega), hwOld1 w hw], fun i => ?_⟩
        refine Fin.cases ?_ ?_ i
        · simp only [Fin.cons_zero]
          rw [hwOld2 p1.2 hbase.2.1, hwNew1]
        · intro j
          simp only [Fin.cons_succ]
          rw [hwNew2 j]
          congr 1
          apply List.map_congr_left
          intro w hw
          rw [hwOld1 w (hws j.succ w hw)]
      · intro D hD
        exact r2.property.2.2.2.2.2.2 D (pushXorListBound B (ws 0) (hws 0) hD)

def pushManyAnd {width : ℕ} (B : Builder width) (n : ℕ)
    (a b : Fin n → ℕ) (ha : ∀ i, a i < width + B.gates.length) (hb : ∀ i, b i < width + B.gates.length) :
    { p : Builder width × (Fin n → ℕ) //
      B.gates.length ≤ p.1.gates.length ∧
      (∀ i, p.2 i < width + p.1.gates.length) ∧
      p.1.nlCount = B.nlCount + n ∧
      (∀ D, (∀ i, (B.depths).getD (a i) 0 ≤ D) → (∀ i, (B.depths).getD (b i) 0 ≤ D) →
        ∀ i, (p.1.depths).getD (p.2 i) 0 ≤ D + 1) ∧
      (∀ w < width + B.gates.length, (p.1.depths).getD w 0 = (B.depths).getD w 0) ∧
      (∀ x : List Bool, x.length = width →
        (∀ w < width + B.gates.length, (p.1.wires x).getD w false = (B.wires x).getD w false) ∧
        ∀ i, b2f ((p.1.wires x).getD (p.2 i) false) =
          b2f ((B.wires x).getD (a i) false) * b2f ((B.wires x).getD (b i) false)) ∧
      (∀ D, DepthBound B (D+1) → (∀ i, B.depths.getD (a i) 0 ≤ D) →
        (∀ i, B.depths.getD (b i) 0 ≤ D) → DepthBound p.1 (D+1)) } := by
  induction n generalizing B with
  | zero =>
    exact ⟨(B, Fin.elim0), le_refl _, fun i => i.elim0, by simp, fun _ _ _ i => i.elim0,
      fun _ _ => rfl, ⟨fun _ _ => ⟨fun _ _ => rfl, fun i => i.elim0⟩, fun _ h _ _ => h⟩⟩
  | succ n ih =>
    let p1 := B.push ⟨GateOp.and, [a 0, b 0]⟩ (by
      intro i hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact ha 0
      · exact hb 0) (by simp)
    have hlen1 : B.gates.length ≤ p1.1.gates.length := by rw [builder_push_len]; omega
    have hout1 : p1.2 < width + p1.1.gates.length := by simp [p1, Builder.push]
    let r2 := ih p1.1 (fun i => a i.succ) (fun i => b i.succ)
      (fun i => lt_of_lt_of_le (ha i.succ) (Nat.add_le_add_left hlen1 width))
      (fun i => lt_of_lt_of_le (hb i.succ) (Nat.add_le_add_left hlen1 width))
    refine ⟨(r2.val.1, Fin.cons p1.2 r2.val.2), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact le_trans hlen1 r2.property.1
    · intro i
      refine Fin.cases ?_ ?_ i
      · simp only [Fin.cons_zero]
        have := r2.property.1
        omega
      · intro j; simp only [Fin.cons_succ]; exact r2.property.2.1 j
    · rw [r2.property.2.2.1, builder_push_nlCount, nonlinear_and]
      simp only [Bool.toNat_true]
      omega
    · intro D hDa hDb i
      refine Fin.cases ?_ ?_ i
      · simp only [Fin.cons_zero]
        rw [r2.property.2.2.2.2.1 p1.2 hout1, builder_push_depths_new]
        simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, nonlinear_and, Bool.toNat_true]
        have := hDa 0
        have := hDb 0
        omega
      · intro j
        simp only [Fin.cons_succ]
        refine r2.property.2.2.2.1 D ?_ ?_ j
        · intro k; rw [builder_push_depths_old B _ _ _ _ (ha k.succ)]; exact hDa k.succ
        · intro k; rw [builder_push_depths_old B _ _ _ _ (hb k.succ)]; exact hDb k.succ
    · intro w hw
      rw [r2.property.2.2.2.2.1 w (by omega), builder_push_depths_old B _ _ _ w hw]
    · constructor
      · intro x hx
        obtain ⟨hwOld2, hwNew2⟩ := r2.property.2.2.2.2.2.1 x hx
        refine ⟨fun w hw => by rw [hwOld2 w (by omega), builder_push_wires_old B _ _ _ x hx w hw], fun i => ?_⟩
        refine Fin.cases ?_ ?_ i
        · simp only [Fin.cons_zero]
          rw [hwOld2 p1.2 hout1, builder_push_wires_new B _ _ _ x hx]
          simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
          exact b2f_and _ _
        · intro j
          simp only [Fin.cons_succ]
          rw [hwNew2 j, builder_push_wires_old B _ _ _ x hx _ (ha j.succ),
            builder_push_wires_old B _ _ _ x hx _ (hb j.succ)]
      · intro D hD hDa hDb
        apply r2.property.2.2.2.2.2.2 D
        · apply pushDepthBound (T := D) B _ _ _ hD
          · intro i hi
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
            rcases hi with rfl | rfl
            · exact hDa 0
            · exact hDb 0
          · simp [nonlinear_and]
        · intro i
          rw [builder_push_depths_old B _ _ _ _ (ha i.succ)]
          exact hDa i.succ
        · intro i
          rw [builder_push_depths_old B _ _ _ _ (hb i.succ)]
          exact hDb i.succ

lemma list_sum_finRange_eq {n : ℕ} (f : Fin n → ZMod 2) :
    ((List.finRange n).map f).sum = ∑ i : Fin n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.finRange_succ, List.map_cons, List.sum_cons, List.map_map, Fin.sum_univ_succ]
    exact congrArg (f 0 + ·) (ih (fun i => f i.succ))

lemma list_sum_filter_finRange {n : ℕ} (p : Fin n → Bool) (f : Fin n → ZMod 2) :
    (((List.finRange n).filter p).map f).sum = ∑ i : Fin n, if p i then f i else 0 := by
  rw [← list_sum_finRange_eq]
  have : ∀ (l : List (Fin n)), ((l.filter p).map f).sum = (l.map fun i => if p i then f i else 0).sum := by
    intro l
    induction l with
    | nil => simp
    | cons a rest ih =>
      simp only [List.filter_cons, List.map_cons, List.sum_cons]
      cases hp : p a <;> simp [ih]
  exact this (List.finRange n)

private theorem compileStage (w p : ℕ) (left right : Fin p → List ℕ)
    (hl : ∀ i a, a ∈ left i → a < w) (hr : ∀ i a, a ∈ right i → a < w) :
    ∃ (B : Builder w) (port : Fin p → ℕ), B.nlCount = p ∧ DepthBound B 1 ∧
      (∀ i, port i < w + B.gates.length) ∧
      ∀ xs : List Bool, xs.length = w →
        (∀ a < w, (B.wires xs).getD a false = xs.getD a false) ∧
        ∀ i, b2f ((B.wires xs).getD (port i) false) =
          ((left i).map fun a => b2f (xs.getD a false)).sum *
          ((right i).map fun a => b2f (xs.getD a false)).sum := by
  let B0 := Builder.empty w
  let A := pushManyXor B0 p left (fun i a ha => by simpa [B0, Builder.empty] using hl i a ha)
  let B := pushManyXor A.val.1 p right (fun i a ha => by have := hr i a ha; omega)
  let X := pushManyAnd B.val.1 p A.val.2 B.val.2
    (fun i => by
      have ha := A.property.2.1 i
      have hb := B.property.1
      omega)
    B.property.2.1
  have hb0 : DepthBound B0 0 := by
    intro d hd
    simp [B0, Builder.empty, Builder.depths] at hd
    omega
  have haD := A.property.2.2.2.2.2.2 0 hb0
  have hbD := B.property.2.2.2.2.2.2 0 haD
  have hxD : DepthBound X.val.1 1 := by
    refine X.property.2.2.2.2.2.2 0 ?_
      (fun i => depthBound_input B.val.1 hbD (A.val.2 i))
      (fun i => depthBound_input B.val.1 hbD (B.val.2 i))
    exact fun d hd => (hbD d hd).trans (by decide)
  refine ⟨X.val.1, X.val.2, ?_, hxD, X.property.2.1, ?_⟩
  · rw [X.property.2.2.1, B.property.2.2.1, A.property.2.2.1]
    simp [B0, Builder.empty, Builder.nlCount]
  · intro xs hxs
    obtain ⟨haOld,haNew⟩ := A.property.2.2.2.2.2.1 xs hxs
    obtain ⟨hbOld,hbNew⟩ := B.property.2.2.2.2.2.1 xs hxs
    obtain ⟨hxOld,hxNew⟩ := X.property.2.2.2.2.2.1 xs hxs
    refine ⟨fun a ha => ?_, fun i => ?_⟩
    · rw [hxOld a (by omega), hbOld a (by omega), haOld a (by omega)]
      rfl
    · rw [hxNew i, hbOld _ (A.property.2.1 i), haNew i, hbNew i]
      congr 1
      apply congrArg List.sum
      apply List.map_congr_left
      intro a ha
      rw [haOld a (by have := hr i a ha; omega)]
      rfl

private def oneBank {n m : ℕ} (a : Fin n → Field) (b : Fin m → Field) : List ℕ :=
  ((List.finRange n).filter (fun i => decide (a i = 1))).map Fin.val ++
    ((List.finRange m).filter (fun i => decide (b i = 1))).map (fun i => n+i.val)

private theorem oneBank_bound {n m : ℕ} (a : Fin n → Field) (b : Fin m → Field) :
    ∀ i ∈ oneBank a b, i < n+m := by
  intro i hi
  rw [oneBank, List.mem_append] at hi
  obtain hi | hi := hi
  · obtain ⟨a,_,rfl⟩ := List.mem_map.mp hi
    have := a.isLt
    omega
  · obtain ⟨b,_,rfl⟩ := List.mem_map.mp hi
    have := b.isLt
    omega

private theorem oneBank_sum {n m : ℕ} (a : Fin n → Field) (b : Fin m → Field)
    (x : Fin n) (y : Fin m) (inp : List Bool)
    (h : ∀ i < n+m, inp.getD i false = (oneEach x y).getD i false) :
    ((oneBank a b).map (fun i => b2f (inp.getD i false))).sum = a x + b y := by
  classical
  simp only [oneBank, List.map_append, List.sum_append, List.map_map, Function.comp_def,
    list_sum_filter_finRange]
  congr 1
  · have hx (i : Fin n) : inp.getD i.val false = decide (i=x) := by
      rw [h _ (by have := i.isLt; omega), oneEach_getD_left x y _ i.isLt]
    simp only [hx]
    rw [Finset.sum_eq_single x]
    · rcases f2_cases (a x) with hz | ho
      · simp [hz, b2f]
      · simp [ho, b2f]
    · intro j _ hj; simp [hj, b2f]
    · simp
  · have hy (i : Fin m) : inp.getD (n+i.val) false = decide (i=y) := by
      rw [h _ (by have := i.isLt; omega), oneEach_getD_right x y _ i.isLt]
    simp only [hy]
    rw [Finset.sum_eq_single y]
    · rcases f2_cases (b y) with hz | ho
      · simp [hz, b2f]
      · simp [ho, b2f]
    · intro j _ hj; simp [hj, b2f]
    · simp

private def selected {n : ℕ} (ix : Fin n → ℕ) (coeff : Fin n → Field) : List ℕ :=
  ((List.finRange n).filter (fun i => decide (coeff i = 1))).map ix

private theorem selected_bound {n w : ℕ} (ix : Fin n → ℕ) (coeff : Fin n → Field)
    (h : ∀ i, ix i < w) : ∀ j ∈ selected ix coeff, j < w := by
  intro j hj
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hj
  exact h i

private theorem selected_sum {n : ℕ} (ix : Fin n → ℕ) (coeff : Fin n → Field)
    (inp : List Bool) :
    ((selected ix coeff).map (fun j => b2f (inp.getD j false))).sum =
      ∑ i : Fin n, coeff i * b2f (inp.getD (ix i) false) := by
  classical
  simp only [selected, List.map_map, Function.comp_def, list_sum_filter_finRange]
  apply Finset.sum_congr rfl
  intro i _
  rcases f2_cases (coeff i) with h0 | h1
  · simp [h0]
  · simp [h1]

private def Fits (n m s k : ℕ) (G : Fin n → Fin m → Bool) : Prop :=
  ∃ (C : Circuit) (cut : ℕ), cut ≤ C.gates.length ∧
    ReadsBack (n+m) C ∧
    (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
    (C.gates.take cut).countP nonlinear ≤ s ∧ (C.gates.drop cut).countP nonlinear ≤ k ∧
    (∀ d ∈ depths (n+m) ⟨C.gates.take cut,0⟩, d ≤ 1) ∧
    (∀ d ∈ depths (n+m+cut) ⟨C.gates.drop cut,0⟩, d ≤ 1) ∧ Represents G C

private theorem bitOfField (a : Field) : b2f (decide (a = 1)) = a := by
  rcases f2_cases a with rfl | rfl <;> decide

private theorem buildPolynomial (n m s k : ℕ)
    (pa pa' : Fin s → Fin n → Field) (pb pb' : Fin s → Fin m → Field)
    (Aout : Fin n → Field) (Bout : Fin m → Field) (cout : Fin s → Field)
    (U U' : Fin k → Fin n → Field) (V V' : Fin k → Fin m → Field)
    (mu nu : Fin k → Fin s → Field) :
    let P := fun i x y => pa i x * pb' i y + pa' i x * pb i y
    let M := fun x y => Aout x + Bout y + (∑ i : Fin s, cout i * P i x y) +
      ∑ j : Fin k,
        (U j x + V j y + ∑ i : Fin s, mu j i * P i x y) *
        (U' j x + V' j y + ∑ i : Fin s, nu j i * P i x y)
    Fits n m s k (fun x y => decide (M x y = 1)) := by
  classical
  intro P M
  let w := n+m
  let low := fun i : Fin s => oneBank (pa i) (pb i)
  let high := fun i : Fin s => oneBank (pa' i) (pb' i)
  obtain ⟨pre, port, preCount, preDepth, preBound, preEval⟩ :=
    compileStage w s low high (fun i => oneBank_bound _ _) (fun i => oneBank_bound _ _)
  let w2 := w + pre.gates.length
  let prepReads := fun (c : Fin s → Field) (a : Fin n → Field) (b : Fin m → Field) =>
    oneBank (fun x => a x + ∑ i, c i * pa i x * pa' i x)
      (fun y => b y + ∑ i, c i * pb i y * pb' i y) ++ selected port c
  have prepReadsBound (c : Fin s → Field) (a : Fin n → Field) (b : Fin m → Field) :
      ∀ v ∈ prepReads c a b, v < w2 := by
    intro v hv
    obtain hv | hv := List.mem_append.mp hv
    · have := oneBank_bound _ _ v hv
      change v < n+m at this
      dsimp only [w2,w]
      omega
    · exact selected_bound port c preBound v hv
  have prepWiresLength (x : Fin n) (y : Fin m) :
      (pre.wires (oneEach x y)).length = w2 := by
    rw [Builder.wires, wires_fold_length, oneEach_length]
  have prepReadsSum (c : Fin s → Field) (a : Fin n → Field) (b : Fin m → Field)
      (x : Fin n) (y : Fin m) :
      ((prepReads c a b).map (fun v => b2f ((pre.wires (oneEach x y)).getD v false))).sum =
        a x + b y + ∑ i : Fin s, c i * P i x y := by
    have hpre := preEval (oneEach x y) (oneEach_length x y)
    simp only [prepReads, List.map_append, List.sum_append]
    rw [oneBank_sum _ _ x y _ hpre.1, selected_sum]
    have portEval (i : Fin s) :
        b2f ((pre.wires (oneEach x y)).getD (port i) false) =
          (pa i x + pb i y) * (pa' i x + pb' i y) := by
      rw [hpre.2 i]
      change (((oneBank (pa i) (pb i)).map
        (fun v => b2f ((oneEach x y).getD v false))).sum) *
          (((oneBank (pa' i) (pb' i)).map
            (fun v => b2f ((oneEach x y).getD v false))).sum) = _
      rw [oneBank_sum _ _ x y _ (fun _ _ => rfl), oneBank_sum _ _ x y _ (fun _ _ => rfl)]
    simp only [portEval]
    have expand :
        (∑ i : Fin s, c i * ((pa i x + pb i y) * (pa' i x + pb' i y))) =
          (∑ i : Fin s, c i * pa i x * pa' i x) +
          (∑ i : Fin s, c i * pb i y * pb' i y) +
          ∑ i : Fin s, c i * P i x y := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by dsimp only [P]; ring
    rw [expand]
    ring_nf
    simp only [show (2 : ZMod 2) = 0 by decide, mul_zero, zero_add, add_zero]
  let outL := fun j : Fin k => prepReads (mu j) (U j) (V j)
  let outR := fun j : Fin k => prepReads (nu j) (U' j) (V' j)
  obtain ⟨post, qport, postCount, postDepth, postBound, postEval⟩ :=
    compileStage w2 k outL outR (fun j => prepReadsBound _ _ _) (fun j => prepReadsBound _ _ _)
  let finalReads := prepReads cout Aout Bout ++ (List.finRange k).map qport
  have finalBounds : ∀ i ∈ finalReads, i < w2 + post.gates.length := by
    intro i hi
    obtain hi | hi := List.mem_append.mp hi
    · exact lt_of_lt_of_le (prepReadsBound _ _ _ i hi) (Nat.le_add_right _ _)
    · obtain ⟨j,_,rfl⟩ := List.mem_map.mp hi
      exact postBound j
  let last := post.pushXorList finalReads finalBounds
  have hlast := pushXorList_spec post finalReads finalBounds 1
    (fun i _ => depthBound_input post postDepth i)
  have depthLast : DepthBound last.1 1 := pushXorListBound post finalReads finalBounds postDepth
  let C : Circuit := ⟨pre.gates ++ last.1.gates, last.2⟩
  have hTake : C.gates.take pre.gates.length = pre.gates := by simp [C]
  have hDrop : C.gates.drop pre.gates.length = last.1.gates := by simp [C]
  refine ⟨C, pre.gates.length, by simp [C], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj i hi
    change j < (pre.gates ++ last.1.gates).length at hj
    change i ∈ ((pre.gates ++ last.1.gates).getD j ⟨GateOp.or,[]⟩).inputs at hi
    by_cases jLeft : j < pre.gates.length
    · rw [getD_append_left _ _ _ _ jLeft] at hi
      exact pre.hRB j jLeft i hi
    · rw [getD_append_right _ _ _ _ (by omega)] at hi
      have hjR : j-pre.gates.length < last.1.gates.length := by
        simp only [List.length_append] at hj
        omega
      have hb := last.1.hRB (j-pre.gates.length) hjR i hi
      dsimp only [w2,w] at hb
      omega
  · intro g h
    obtain h | h := List.mem_append.mp h
    · exact pre.hFan g h
    · exact last.1.hFan g h
  · rw [hTake]
    exact le_of_eq preCount
  · rw [hDrop]
    exact le_of_eq (hlast.2.2.1.trans postCount)
  · rw [hTake]
    exact preDepth
  · rw [hDrop]
    exact depthLast
  · intro x y
    apply b2f_injective
    rw [bitOfField]
    let inp := pre.wires (oneEach x y)
    have hinp : inp.length = w2 := prepWiresLength x y
    have hp := postEval inp hinp
    have hval := (hlast.2.2.2.2.2 inp hinp).2
    unfold Circuit.eval
    change b2f (((pre.gates ++ last.1.gates).foldl wiresStep (oneEach x y)).getD last.2 false) = M x y
    rw [List.foldl_append]
    change b2f ((last.1.wires inp).getD last.2 false) = M x y
    rw [hval]
    simp only [finalReads, List.map_append, List.sum_append, List.map_map, Function.comp_def,
      list_sum_finRange_eq]
    have hOut : ((prepReads cout Aout Bout).map
        (fun v => b2f ((post.wires inp).getD v false))).sum =
        Aout x + Bout y + ∑ i : Fin s, cout i * P i x y := by
      rw [← prepReadsSum cout Aout Bout x y]
      congr 1
      apply List.map_congr_left
      intro i hi
      rw [hp.1 i (prepReadsBound _ _ _ i hi)]
    rw [hOut]
    dsimp only [M]
    apply congrArg (fun z : Field => Aout x + Bout y + (∑ i : Fin s, cout i * P i x y) + z)
    apply Finset.sum_congr rfl
    intro j _
    rw [hp.2 j]
    change (((prepReads (mu j) (U j) (V j)).map
      (fun v => b2f (inp.getD v false))).sum) *
        (((prepReads (nu j) (U' j) (V' j)).map
          (fun v => b2f (inp.getD v false))).sum) = _
    rw [prepReadsSum _ _ _ x y, prepReadsSum _ _ _ x y]

private theorem rawEvalIndependent (B : Type) [Fintype B] [DecidableEq B] :
    LinearIndependent Field (fun i : B => fun x : B → Field => x i) := by
  rw [Fintype.linearIndependent_iff]
  intro v hv i
  have h := congrFun hv (Pi.single i (1 : Field))
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
  rwa [Finset.sum_eq_single i, Pi.single_eq_same, mul_one] at h
  · intro j _ hj; simp [Pi.single_eq_of_ne hj]
  · simp

private theorem rawEvalRank (B : Type) [Fintype B] [DecidableEq B] :
    Matrix.rank (m := B → Field) (n := B → Field)
      (fun x y => ∑ i : B, x i * y i) = Fintype.card B := by
  let L : Matrix (B → Field) B Field := fun x i => x i
  let R : Matrix B (B → Field) Field := fun i x => x i
  have hL : L.rank = Fintype.card B := by
    rw [← Matrix.rank_transpose L]
    exact LinearIndependent.rank_matrix (rawEvalIndependent B)
  have hR : R.rank = Fintype.card B := LinearIndependent.rank_matrix (rawEvalIndependent B)
  change (L * R).rank = _
  have le := Matrix.rank_mul_le_left L R
  have ge := Matrix.rank_mul_ge L R
  omega

set_option maxHeartbeats 2000000 in
private theorem attainable (s k : ℕ) :
    ∃ (n m : ℕ) (G : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m),
      Fits n m s k G ∧ (anchor u v (fun x y => b2f (G x y))).rank =
        if k = 0 then 2*s else 2*k+4*s+4*(turanPairs s k).card := by
  classical
  by_cases zeroK : k = 0
  · subst k
    let W := Base s → Field
    let N := Fintype.card W
    let e : Fin N ≃ W := (Fintype.equivFin W).symm
    let root := e.symm 0
    let A : Matrix W W Field := fun x y => ∑ i : Base s, x i * y i
    let G : Fin N → Fin N → Bool := fun x y => decide (A (e x) (e y) = 1)
    refine ⟨N,N,G,root,root,?_,?_⟩
    · have h := buildPolynomial N N s 0 (fun i x => e x (i,false)) (fun i x => e x (i,true))
        (fun i y => e y (i,true)) (fun i y => e y (i,false)) 0 0 1 0 0 0 0 0 0
      simpa [G, A, Base, Fintype.sum_prod_type, Fintype.sum_bool, add_comm] using h
    · simp only [ite_eq_left rfl]
      have eq : anchor root root (fun x y => b2f (G x y)) = A.submatrix e e := by
        ext x y
        rw [Matrix.submatrix_apply]
        simp only [anchor, G, bitOfField, root, Equiv.apply_symm_apply, A]
        change ((∑ i : Base s, e x i * e y i) +
          (∑ i : Base s, e x i * (0 : Base s → Field) i) +
          (∑ i : Base s, (0 : Base s → Field) i * e y i) +
          (∑ i : Base s, (0 : Base s → Field) i * (0 : Base s → Field) i)) =
          ∑ i : Base s, e x i * e y i
        simp only [Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
      rw [eq, Matrix.rank_submatrix]
      have h := rawEvalRank (Base s)
      change A.rank = 2*s
      rw [h]
      simp [Base, mul_comm]
  · have hk : 0 < k := Nat.pos_of_ne_zero zeroK
    let W := Assignment s k
    let N := Fintype.card W
    let e : Fin N ≃ W := (Fintype.equivFin W).symm
    let root := e.symm 0
    let G : Fin N → Fin N → Bool := fun x y => decide (twoStageValue (e x) (e y) = 1)
    refine ⟨N,N,G,root,root,?_,?_⟩
    · have h := buildPolynomial N N s k (fun i x => e x (.inr (i,false)))
        (fun i x => e x (.inr (i,true))) (fun i y => e y (.inr (i,true)))
        (fun i y => e y (.inr (i,false))) 0 0 0
        (fun j x => e x (.inl (j,false))) (fun j x => e x (.inl (j,true)))
        (fun j y => e y (.inl (j,true))) (fun j y => e y (.inl (j,false)))
        (fun j i => uCoeff i j) (fun j i => vCoeff i j)
      have hP (i : Fin s) (x y : Fin N) :
          e x (.inr (i,false)) * e y (.inr (i,false)) +
            e x (.inr (i,true)) * e y (.inr (i,true)) = prepValue (e x) (e y) i := by
        simp only [prepValue, Fintype.sum_bool]
        ring
      dsimp only at h
      simp only [Pi.zero_apply, zero_mul, zero_add, Finset.sum_const_zero, add_zero, hP] at h
      convert h using 1
      ext x y
      simp only [G, twoStageValue]
      apply decide_eq_decide.mpr
      rfl
    · simp only [ite_eq_right zeroK]
      let A : Matrix W W Field := fun x y =>
        ∑ i : Feature s k, feat lc 0 x i * feat rc (diagonal (k := k)) y (flipFeature i)
      have eq : anchor root root (fun x y => b2f (G x y)) = A.submatrix e e := by
        ext x y
        simp only [anchor, G, bitOfField, root, Equiv.apply_symm_apply, A, Matrix.submatrix_apply]
        exact polynomialFeatureExpansion (e x) (e y)
      rw [eq, Matrix.rank_submatrix]
      exact featureRank s k lc rc diagonal (lc_nonzero hk) (rc_nonzero hk)

end PEqualNP.Outside.L_meta_33679

theorem PEqualNP.Outside.L_meta_33679 : (
let nonlinear := fun (g : PEqualNP.CircuitLowerBounds.Gate) =>
  (g.inputs.length == 2) &&
  xor (xor (g.op.eval [false, false]) (g.op.eval [false, true]))
      (xor (g.op.eval [true, false]) (g.op.eval [true, true]))
let depths := fun (width : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
  C.gates.foldl (fun (ds : List ℕ) g =>
    ds ++ [(g.inputs.map (fun a => ds.getD a 0)).foldr max 0 + (nonlinear g).toNat])
    (List.replicate width 0)
let F := ZMod 2
∀ s k : ℕ,
  let pairs := ((Finset.univ : Finset (Fin s × Fin s)).filter (fun ij =>
    ij.1 < ij.2 ∧ ij.1.val % (2*k+1) ≠ ij.2.val % (2*k+1))).card
  let bound := if k = 0 then 2*s else 2*k+4*s+4*pairs
  let fit := fun (n m : ℕ) (G : Fin n → Fin m → Bool) =>
    ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (cut : ℕ), cut ≤ C.gates.length ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (n+m) C ∧
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) ∧
      (C.gates.take cut).countP nonlinear ≤ s ∧ (C.gates.drop cut).countP nonlinear ≤ k ∧
      (∀ d ∈ depths (n+m) ⟨C.gates.take cut,0⟩, d ≤ 1) ∧
      (∀ d ∈ depths (n+m+cut) ⟨C.gates.drop cut,0⟩, d ≤ 1) ∧
      PEqualNP.Represents.Represents G C
  let rk := fun {n m : ℕ} (G : Fin n → Fin m → Bool) (u : Fin n) (v : Fin m) =>
    let bit := fun i j => if G i j then (1 : F) else 0
    let X : Matrix (Fin n) (Fin m) F := fun i j => bit i j + bit i v + bit u j + bit u v
    X.rank
  IsGreatest {r : ℕ | ∃ (n m : ℕ) (G : Fin n → Fin m → Bool)
    (u : Fin n) (v : Fin m), fit n m G ∧ rk G u v = r} bound) := by
  dsimp only
  intro s k
  constructor
  · exact PEqualNP.Outside.L_meta_33679.attainable s k
  · intro r hr
    obtain ⟨n, m, G, u, v, ⟨C, cut, hcut, hRB, hFan, hL, hR, hDepthL, hDepthR, hRep⟩, rfl⟩ := hr
    exact PEqualNP.Outside.L_meta_33679.circuitRankUpper n m s k u v G C cut
      hcut hRB hFan hL hR hDepthL hDepthR hRep
