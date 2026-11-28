import Mathlib

namespace PEqualNP.Outside.L_lib_876

open Module

abbrev K2 := ZMod 2

def det3 (a b c : Fin 3 → K2) : K2 :=
  a 0 * (b 1 * c 2 + b 2 * c 1) + a 1 * (b 0 * c 2 + b 2 * c 0) + a 2 * (b 0 * c 1 + b 1 * c 0)

lemma two0 : (2 : K2) = 0 := by decide

lemma add_self0 (x : K2) : x + x = 0 := CharTwo.add_self_eq_zero x

section Abstract

variable {V : Type} [AddCommGroup V] [Module K2 V]

def Good (T : V →ₗ[K2] V →ₗ[K2] V →ₗ[K2] K2) (v : V) : Prop :=
  ∃ a b, T v a b = 1 ∧ ∀ x y, T v x y = T v a x * T v b y + T v b x * T v a y

lemma good_plucker {T : V →ₗ[K2] V →ₗ[K2] V →ₗ[K2] K2} {v : V} (h : Good T v) (a b c d : V)
    (h1 : T v a b = 1) (h2 : T v c d = 1) (h3 : T v a c = 0) (h4 : T v a d = 0) : False := by
  obtain ⟨p, q, _, h⟩ := h
  have key : T v a b * T v c d + T v a c * T v b d + T v a d * T v b c = 0 := by
    rw [h a b, h c d, h a c, h b d, h a d, h b c]
    ring_nf
    simp [two0, show (4 : K2) = 0 by decide, show (6 : K2) = 0 by decide]
  rw [h1, h2, h3, h4] at key
  simp at key

def pull {W : Type} [AddCommGroup W] [Module K2 W] (T : V →ₗ[K2] V →ₗ[K2] V →ₗ[K2] K2)
    (f : W →ₗ[K2] V) : W →ₗ[K2] W →ₗ[K2] W →ₗ[K2] K2 where
  toFun a := (T (f a)).compl₁₂ f f
  map_add' a b := by
    apply LinearMap.ext; intro x; apply LinearMap.ext; intro y
    simp [LinearMap.compl₁₂_apply]
  map_smul' c a := by
    apply LinearMap.ext; intro x; apply LinearMap.ext; intro y
    simp [LinearMap.compl₁₂_apply]

@[simp] lemma pull_apply {W : Type} [AddCommGroup W] [Module K2 W]
    (T : V →ₗ[K2] V →ₗ[K2] V →ₗ[K2] K2) (f : W →ₗ[K2] V) (a b c : W) :
    pull T f a b c = T (f a) (f b) (f c) := rfl

end Abstract

lemma ne_zero_one (x : K2) (h : x ≠ 0) : x = 1 := by
  revert x; decide

set_option maxHeartbeats 1000000 in
theorem splitting : ∀ (k : ℕ) (V : Type) [AddCommGroup V] [Module K2 V] [FiniteDimensional K2 V]
    (T : V →ₗ[K2] V →ₗ[K2] V →ₗ[K2] K2), finrank K2 V = k →
    (∀ a b c, T a b c = T b a c) → (∀ a b c, T a b c = T a c b) → (∀ a b, T a a b = 0) →
    Submodule.span K2 ({v | Good T v} ∪ {v | T v = 0}) = ⊤ →
    ∃ (c : ℕ) (L : V →ₗ[K2] (Fin c × Fin 3 → K2)), Function.Surjective L ∧
      ∀ x y z, T x y z = ∑ i : Fin c,
        det3 (fun j => L x (i,j)) (fun j => L y (i,j)) (fun j => L z (i,j)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro V _ _ _ T hk s1 s2 alt hspan
  by_cases hT : ∀ x y z, T x y z = 0
  · refine ⟨0, 0, ?_, ?_⟩
    · intro y; exact ⟨0, funext fun p => p.1.elim0⟩
    · intro x y z; simp [hT]
  have triple : ∃ u1 u2 u3, Good T u1 ∧ Good T u2 ∧ Good T u3 ∧ T u1 u2 u3 = 1 := by
    by_contra hno
    have h0 : ∀ u1 ∈ ({v | Good T v} ∪ {v | T v = 0} : Set V),
        ∀ u2 ∈ ({v | Good T v} ∪ {v | T v = 0} : Set V),
        ∀ u3 ∈ ({v | Good T v} ∪ {v | T v = 0} : Set V), T u1 u2 u3 = 0 := by
      intro u1 h1 u2 h2 u3 h3
      rcases h1 with h1 | h1
      swap
      · have h1' : T u1 = 0 := h1
        simp [h1']
      rcases h2 with h2 | h2
      swap
      · have h2' : T u2 = 0 := h2
        rw [s1]; simp [h2']
      rcases h3 with h3 | h3
      swap
      · have h3' : T u3 = 0 := h3
        rw [s2, s1]; simp [h3']
      by_contra hne
      exact hno ⟨u1, u2, u3, h1, h2, h3, ne_zero_one _ hne⟩
    apply hT
    have e1 : ∀ u1 ∈ ({v | Good T v} ∪ {v | T v = 0} : Set V),
        ∀ u2 ∈ ({v | Good T v} ∪ {v | T v = 0} : Set V), T u1 u2 = 0 := by
      intro u1 h1 u2 h2
      apply LinearMap.ext_on hspan
      intro u3 h3
      simpa using h0 u1 h1 u2 h2 u3 h3
    have e2 : ∀ u1 ∈ ({v | Good T v} ∪ {v | T v = 0} : Set V), T u1 = 0 := by
      intro u1 h1
      apply LinearMap.ext_on hspan
      intro u2 h2
      simpa using e1 u1 h1 u2 h2
    have e3 : T = 0 := by
      apply LinearMap.ext_on hspan
      intro u1 h1
      simpa using e2 u1 h1
    intro x y z
    simp [e3]
  obtain ⟨u1, u2, u3, g1, g2, g3, h123⟩ := triple
  have h132 : T u1 u3 u2 = 1 := by rw [s2]; exact h123
  have h213 : T u2 u1 u3 = 1 := by rw [s1]; exact h123
  have h231 : T u2 u3 u1 = 1 := by rw [s2]; exact h213
  have h312 : T u3 u1 u2 = 1 := by rw [s1]; exact h132
  have h321 : T u3 u2 u1 = 1 := by rw [s2]; exact h312
  have alt2 : ∀ a b, T a b a = 0 := fun a b => by rw [s2]; exact alt a b
  have alt3 : ∀ a b, T b a a = 0 := fun a b => by rw [s1]; exact alt2 a b
  let u : Fin 3 → V := ![u1, u2, u3]
  let l : V →ₗ[K2] (Fin 3 → K2) := LinearMap.pi ![T u2 u3, T u3 u1, T u1 u2]
  let s : (Fin 3 → K2) →ₗ[K2] V := Fintype.linearCombination K2 u
  have s_ap : ∀ α, s α = α 0 • u1 + α 1 • u2 + α 2 • u3 := by
    intro α
    simp [s, u, Fintype.linearCombination_apply, Fin.sum_univ_three]
  have l0 : ∀ x, l x 0 = T u2 u3 x := fun x => rfl
  have l1 : ∀ x, l x 1 = T u3 u1 x := fun x => rfl
  have l2 : ∀ x, l x 2 = T u1 u2 x := fun x => rfl
  have ls : ∀ α, l (s α) = α := by
    intro α
    funext j
    fin_cases j
    · change T u2 u3 (s α) = α 0
      simp [s_ap, h231, alt2, alt3]
    · change T u3 u1 (s α) = α 1
      simp [s_ap, h312, alt2, alt3]
    · change T u1 u2 (s α) = α 2
      simp [s_ap, h123, alt2, alt3]
  -- contraction with a triple vector is determined by the coordinates
  have rep : ∀ (v a b : V), Good T v → T v a b = 1 → ∀ x y,
      T v x y = T v a x * T v b y + T v b x * T v a y := by
    intro v a b hv hab x y
    obtain ⟨p, q, _, h⟩ := hv
    have key : T v x y * T v a b = T v a x * T v b y + T v b x * T v a y := by
      rw [h x y, h a b, h a x, h b y, h b x, h a y]
      ring_nf
      simp [two0, show (4 : K2) = 0 by decide, show (6 : K2) = 0 by decide]
    rwa [hab, mul_one] at key
  have kill : ∀ z, l z = 0 → ∀ (j : Fin 3) (w : V), T (u j) z w = 0 := by
    intro z hz j w
    have z0 : T u2 u3 z = 0 := by rw [← l0, hz]; rfl
    have z1 : T u3 u1 z = 0 := by rw [← l1, hz]; rfl
    have z2 : T u1 u2 z = 0 := by rw [← l2, hz]; rfl
    have a1 : T u1 u3 z = 0 := by rw [s1]; exact z1
    have a2 : T u2 u1 z = 0 := by rw [s1]; exact z2
    have a3 : T u3 u2 z = 0 := by rw [s1]; exact z0
    fin_cases j
    · change T u1 z w = 0
      rw [rep u1 u2 u3 g1 h123 z w]; simp [z2, a1]
    · change T u2 z w = 0
      rw [rep u2 u3 u1 g2 h231 z w]; simp [z0, a2]
    · change T u3 z w = 0
      rw [rep u3 u1 u2 g3 h312 z w]; simp [z1, a3]
  have killS : ∀ α z w, l z = 0 → T (s α) z w = 0 := by
    intro α z w hz
    have k0 : T u1 z w = 0 := kill z hz 0 w
    have k1 : T u2 z w = 0 := kill z hz 1 w
    have k2 : T u3 z w = 0 := kill z hz 2 w
    simp [s_ap, k0, k1, k2]
  let W := LinearMap.ker l
  let π : V →ₗ[K2] W := (LinearMap.id - s ∘ₗ l).codRestrict W (by
    intro x
    simp [W, ls])
  have πv : ∀ x, (π x : V) = x - s (l x) := fun x => rfl
  have lπ : ∀ x, l (π x : V) = 0 := fun x => (π x).2
  have dec : ∀ x, x = s (l x) + (π x : V) := by
    intro x; rw [πv]; abel
  have cube : ∀ α β γ, T (s α) (s β) (s γ) = det3 α β γ := by
    intro α β γ
    simp only [s_ap, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      alt, alt2, alt3, h123, h132, h213, h231, h312, h321, det3]
    ring
  have split : ∀ x y z, T x y z = det3 (l x) (l y) (l z) + T (π x : V) (π y : V) (π z : V) := by
    intro x y z
    conv_lhs => rw [dec x, dec y, dec z]
    have m1 : ∀ α z' γ, l z' = 0 → T (s α) z' (s γ) = 0 := fun α z' γ h => killS α z' _ h
    have m2 : ∀ α β z', l z' = 0 → T (s α) (s β) z' = 0 := fun α β z' h => by
      rw [s2]; exact killS α z' _ h
    have m3 : ∀ α z' w, l z' = 0 → T (s α) z' w = 0 := fun α z' w h => killS α z' w h
    have m4 : ∀ α z' w, l z' = 0 → T (s α) w z' = 0 := fun α z' w h => by
      rw [s2]; exact killS α z' w h
    have m5 : ∀ α z' w, l z' = 0 → T z' (s α) w = 0 := fun α z' w h => by
      rw [s1]; exact killS α z' w h
    have m6 : ∀ α z' w, l z' = 0 → T z' w (s α) = 0 := fun α z' w h => by
      rw [s2, s1]; exact killS α z' w h
    have t1 := m3 (l x) (π y) (s (l z)) (lπ y)
    have t2 := m4 (l x) (π z) (s (l y)) (lπ z)
    have t3 := m3 (l x) (π y) (π z) (lπ y)
    have t4 := m5 (l y) (π x) (s (l z)) (lπ x)
    have t5 := m6 (l z) (π x) (s (l y)) (lπ x)
    have t6 : T (π x : V) (π y : V) (s (l z)) = 0 := m6 (l z) (π x) (π y) (lπ x)
    have t7 := m5 (l y) (π x) (π z) (lπ x)
    simp only [map_add, LinearMap.add_apply]
    simp only [t1, t2, t3, t4, t5, t6, t7, cube, add_zero, zero_add]
  have πW : ∀ x : W, π (x : V) = x := by
    intro x
    apply Subtype.ext
    have h : l (x : V) = 0 := x.2
    rw [πv, h, map_zero, sub_zero]
  let T' := pull T W.subtype
  have T'_ap : ∀ a b c : W, T' a b c = T (a : V) (b : V) (c : V) := fun _ _ _ => rfl
  have lt : finrank K2 W < k := by
    have h := l.finrank_range_add_finrank_ker
    have hs : LinearMap.range l = ⊤ := LinearMap.range_eq_top.mpr fun α => ⟨s α, ls α⟩
    rw [hs, finrank_top, finrank_fin_fun, hk] at h
    change finrank K2 (LinearMap.ker l) < k
    omega
  have hsp' : Submodule.span K2 ({v : W | Good T' v} ∪ {v | T' v = 0}) = ⊤ := by
    set S' := Submodule.span K2 ({v : W | Good T' v} ∪ {v | T' v = 0}) with hS'
    have radical : ∀ v : V, (∀ y z : W, T (π v : V) y z = 0) → π v ∈ S' := by
      intro v h
      apply Submodule.subset_span
      right
      change T' (π v) = 0
      apply LinearMap.ext; intro y; apply LinearMap.ext; intro z
      exact h y z
    have le : Submodule.span K2 ({v | Good T v} ∪ {v | T v = 0}) ≤ S'.comap π := by
      rw [Submodule.span_le]
      rintro v (hv | hv)
      swap
      · have hv' : T v = 0 := hv
        apply radical
        intro y z
        rw [πv, map_sub, LinearMap.sub_apply, LinearMap.sub_apply, hv',
          killS (l v) y z y.2]
        simp
      by_cases hl : l v = 0
      · apply Submodule.subset_span
        left
        have e : (π v : V) = v := by rw [πv, hl, map_zero, sub_zero]
        obtain ⟨a, b, hab, h⟩ := hv
        have tr : ∀ (a : V) (x : W), T v a x = T v (π a : V) x := by
          intro a x
          have h1 := split v a x
          have h2 := split v (π a : V) x
          have hx : l (x : V) = 0 := x.2
          rw [πW x] at h1 h2
          have hπ : π (π a : V) = π a := πW (π a)
          rw [hπ, lπ a] at h2
          rw [h1, h2, hl]
          simp [det3]
        have trb : T v a b = T v (π a : V) (π b : V) := by
          have h1 := split v a b
          have h2 := split v (π a : V) (π b : V)
          rw [πW (π a), πW (π b), lπ a, lπ b] at h2
          rw [h1, h2, hl]
          simp [det3]
        refine ⟨π a, π b, ?_, ?_⟩
        · change T (π v : V) (π a : V) (π b : V) = 1
          rw [e, ← trb]; exact hab
        · intro x y
          simp only [T'_ap, e]
          rw [← tr a x, ← tr b y, ← tr b x, ← tr a y]
          exact h x y
      · apply radical
        intro y z
        by_contra hne
        have h1 := ne_zero_one _ hne
        have pick : ∀ α : Fin 3 → K2, α ≠ 0 → ∃ β γ : Fin 3 → K2, det3 α β γ = 1 := by
          unfold det3; decide
        obtain ⟨β, γ, hβγ⟩ := pick (l v) hl
        have hs0 : ∀ α, π (s α) = 0 := by
          intro α
          apply Subtype.ext
          rw [πv, ls, sub_self]; rfl
        have y0 : l (y : V) = 0 := y.2
        have z0 : l (z : V) = 0 := z.2
        apply good_plucker hv (s β) (s γ) y z
        · rw [split, ls, ls, hs0, hs0]
          simp [hβγ]
        · rw [split, y0, z0, πW y, πW z]
          have : det3 (l v) 0 0 = 0 := by simp [det3]
          rw [this, zero_add]; exact h1
        · rw [split, hs0]
          simp [y0, det3]
        · rw [split, hs0]
          simp [z0, det3]
    rw [eq_top_iff]
    intro x _
    have : (x : V) ∈ S'.comap π := le (hspan ▸ Submodule.mem_top)
    rw [Submodule.mem_comap, πW] at this
    exact this
  obtain ⟨c, L', hL', hf⟩ := ih (finrank K2 W) lt W T' rfl
    (fun a b d => s1 _ _ _) (fun a b d => s2 _ _ _) (fun a b => alt _ _) hsp'
  let L : V →ₗ[K2] (Fin (c+1) × Fin 3 → K2) := LinearMap.pi fun p =>
    Fin.cases (motive := fun _ => V →ₗ[K2] K2) (LinearMap.proj p.2 ∘ₗ l)
      (fun i => LinearMap.proj (i, p.2) ∘ₗ L' ∘ₗ π) p.1
  have L0 : ∀ x j, L x (0, j) = l x j := fun x j => rfl
  have LS : ∀ x i j, L x (Fin.succ i, j) = L' (π x) (i, j) := fun x i j => rfl
  refine ⟨c+1, L, ?_, ?_⟩
  · intro t
    obtain ⟨w, hw⟩ := hL' (fun p => t (Fin.succ p.1, p.2))
    let α : Fin 3 → K2 := fun j => t (0, j)
    have h1 : l (s α + (w : V)) = α := by
      have : l (w : V) = 0 := w.2
      rw [map_add, ls, this, add_zero]
    have h2 : π (s α + (w : V)) = w := by
      apply Subtype.ext
      rw [πv, h1, add_sub_cancel_left]
    refine ⟨s α + (w : V), ?_⟩
    funext ⟨i, j⟩
    induction i using Fin.cases with
    | zero => rw [L0, h1]
    | succ i => rw [LS, h2, hw]
  · intro x y z
    rw [Fin.sum_univ_succ]
    simp only [L0, LS]
    rw [split]
    congr 1
    exact hf (π x) (π y) (π z)

-- the split form

section Split

variable {V : Type} [AddCommGroup V] [Module K2 V] {c : ℕ}
  (T : V →ₗ[K2] V →ₗ[K2] V →ₗ[K2] K2) (L : V →ₗ[K2] (Fin c × Fin 3 → K2))

def blk (y : Fin c × Fin 3 → K2) (i : Fin c) : Fin 3 → K2 := fun j => y (i, j)

def embed (i : Fin c) (α : Fin 3 → K2) : Fin c × Fin 3 → K2 :=
  fun p => if p.1 = i then α p.2 else 0

lemma blk_embed_same (i : Fin c) (α : Fin 3 → K2) : blk (embed i α) i = α := by
  funext j; simp [blk, embed]

lemma blk_embed_ne {i k : Fin c} (h : k ≠ i) (α : Fin 3 → K2) : blk (embed i α) k = 0 := by
  funext j; simp [blk, embed, h]

variable (hL : Function.Surjective L)
  (hf : ∀ x y z, T x y z = ∑ i : Fin c, det3 (blk (L x) i) (blk (L y) i) (blk (L z) i))

include hf in
lemma eval_embed (v x y : V) (i : Fin c) (β : Fin 3 → K2) (hx : L x = embed i β) :
    T v x y = det3 (blk (L v) i) β (blk (L y) i) := by
  rw [hf, Finset.sum_eq_single i]
  · rw [hx, blk_embed_same]
  · intro k _ hk
    rw [hx, blk_embed_ne hk]
    simp [det3]
  · simp

lemma pick (α : Fin 3 → K2) (h : α ≠ 0) : ∃ β γ : Fin 3 → K2, det3 α β γ = 1 := by
  revert α; unfold det3; decide

include hL hf in
lemma rad_iff (u : V) : T u = 0 ↔ L u = 0 := by
  constructor
  · intro h
    funext ⟨i, j⟩
    by_contra hne
    have hb : blk (L u) i ≠ 0 := fun e => hne (congrFun e j)
    obtain ⟨β, γ, hβγ⟩ := pick _ hb
    obtain ⟨x, hx⟩ := hL (embed i β)
    obtain ⟨y, hy⟩ := hL (embed i γ)
    have := eval_embed T L hf u x y i β hx
    rw [hy, blk_embed_same, hβγ, h] at this
    simp at this
  · intro h
    apply LinearMap.ext; intro x; apply LinearMap.ext; intro y
    rw [hf, h]
    simp [blk, det3]

include hL hf in
lemma good_iff (u : V) : Good T u ↔ ∃ i α, α ≠ 0 ∧ L u = embed i α := by
  constructor
  · intro hg
    have hne : L u ≠ 0 := by
      intro h
      have h0 := (rad_iff T L hL hf u).2 h
      obtain ⟨a, b, hab, _⟩ := hg
      rw [h0] at hab
      simp at hab
    obtain ⟨⟨i, j⟩, hij⟩ := Function.ne_iff.mp hne
    have hbi : blk (L u) i ≠ 0 := fun e => hij (congrFun e j)
    refine ⟨i, blk (L u) i, hbi, ?_⟩
    funext ⟨k, m⟩
    by_cases hk : k = i
    · subst hk; simp [embed, blk]
    simp only [embed, hk, if_false]
    by_contra hkm
    have hbk : blk (L u) k ≠ 0 := fun e => hkm (congrFun e m)
    obtain ⟨β, γ, hβγ⟩ := pick _ hbi
    obtain ⟨β', γ', hβγ'⟩ := pick _ hbk
    obtain ⟨a, ha⟩ := hL (embed i β)
    obtain ⟨b, hb⟩ := hL (embed i γ)
    obtain ⟨x, hx⟩ := hL (embed k β')
    obtain ⟨y, hy⟩ := hL (embed k γ')
    apply good_plucker hg a b x y
    · rw [eval_embed T L hf u a b i β ha, hb, blk_embed_same, hβγ]
    · rw [eval_embed T L hf u x y k β' hx, hy, blk_embed_same, hβγ']
    · rw [eval_embed T L hf u a x i β ha, hx, blk_embed_ne (Ne.symm hk)]
      simp [det3]
    · rw [eval_embed T L hf u a y i β ha, hy, blk_embed_ne (Ne.symm hk)]
      simp [det3]
  · rintro ⟨i, α, hα, hu⟩
    have form : ∀ x y, T u x y = det3 α (blk (L x) i) (blk (L y) i) := by
      intro x y
      rw [hf, Finset.sum_eq_single i]
      · rw [hu, blk_embed_same]
      · intro k _ hk
        rw [hu, blk_embed_ne hk]
        simp [det3]
      · simp
    obtain ⟨β, γ, hβγ⟩ := pick α hα
    obtain ⟨a, ha⟩ := hL (embed i β)
    obtain ⟨b, hb⟩ := hL (embed i γ)
    refine ⟨a, b, ?_, ?_⟩
    · rw [form, ha, hb, blk_embed_same, blk_embed_same, hβγ]
    · intro x y
      simp only [form, ha, hb, blk_embed_same]
      have key : det3 α (blk (L x) i) (blk (L y) i) * det3 α β γ
          = det3 α β (blk (L x) i) * det3 α γ (blk (L y) i)
            + det3 α γ (blk (L x) i) * det3 α β (blk (L y) i) := by
        unfold det3
        ring_nf
        simp [two0, show (4 : K2) = 0 by decide, show (6 : K2) = 0 by decide]
      rwa [hβγ, mul_one] at key

include hL hf in
lemma span_top : Submodule.span K2 ({v | Good T v} ∪ {v | T v = 0}) = ⊤ := by
  set S := Submodule.span K2 ({v | Good T v} ∪ {v | T v = 0}) with hS
  rw [eq_top_iff]
  intro x _
  have lift : ∀ i : Fin c, ∃ z, L z = embed i (blk (L x) i) := fun i => hL _
  choose z hz using lift
  have hzS : ∀ i, z i ∈ S := by
    intro i
    apply Submodule.subset_span
    by_cases h : blk (L x) i = 0
    · right
      apply (rad_iff T L hL hf _).2
      rw [hz, h]
      funext p; simp [embed]
    · left
      exact (good_iff T L hL hf _).2 ⟨i, _, h, hz i⟩
  have hr : x - ∑ i, z i ∈ S := by
    apply Submodule.subset_span
    right
    apply (rad_iff T L hL hf _).2
    rw [map_sub, map_sum, sub_eq_zero]
    funext ⟨k, m⟩
    simp only [hz, Finset.sum_apply, embed]
    rw [Finset.sum_ite_eq]
    simp [blk]
  have := S.add_mem hr (S.sum_mem (t := Finset.univ) (fun i _ => hzS i))
  simpa using this

include hL hf in
lemma good_card [Fintype V] [DecidableEq V] [DecidablePred (Good T)] :
    (Finset.univ.filter (Good T)).card = c * 7 * 2 ^ finrank K2 (LinearMap.ker L) := by
  classical
  let N : Finset (Fin 3 → K2) := Finset.univ.filter (fun α => α ≠ 0)
  have hN : N.card = 7 := by decide
  let Y : Finset (Fin c × Fin 3 → K2) :=
    (Finset.univ ×ˢ N).image (fun p => embed p.1 p.2)
  have hY : Y.card = c * 7 := by
    rw [Finset.card_image_of_injOn, Finset.card_product, hN, Finset.card_univ, Fintype.card_fin]
    rintro ⟨i, α⟩ h ⟨k, β⟩ _ e
    have hα : α ≠ 0 := by
      have := (Finset.mem_product.mp h).2
      simpa [N] using this
    simp only at e
    have hik : i = k := by
      by_contra hne
      have := congrArg (fun y => blk y i) e
      simp only [blk_embed_same, blk_embed_ne hne] at this
      exact hα this
    subst hik
    have := congrArg (fun y => blk y i) e
    simp only [blk_embed_same] at this
    rw [this]
  have mem : ∀ u, Good T u ↔ L u ∈ Y := by
    intro u
    rw [good_iff T L hL hf]
    simp only [Y, N, Finset.mem_image, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_filter, Prod.exists]
    constructor
    · rintro ⟨i, α, h, e⟩; exact ⟨i, α, h, e.symm⟩
    · rintro ⟨i, α, h, e⟩; exact ⟨i, α, h, e.symm⟩
  have hker : (Finset.univ.filter (fun u => L u = 0)).card = 2 ^ finrank K2 (LinearMap.ker L) := by
    have h := Module.card_eq_pow_finrank (K := K2) (V := LinearMap.ker L)
    rw [ZMod.card] at h
    rw [← h]
    exact (Fintype.card_of_subtype _ (fun u => by simp)).symm
  have fib : ∀ y ∈ Y, ((Finset.univ.filter (Good T)).filter (fun u => L u = y)).card
      = 2 ^ finrank K2 (LinearMap.ker L) := by
    intro y hy
    obtain ⟨w, hw⟩ := hL y
    rw [← hker]
    apply Finset.card_bij' (fun u _ => u - w) (fun u _ => u + w)
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      rw [map_sub, hu.2, hw, sub_self]
    · intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      have e : L (u + w) = y := by rw [map_add, hu, hw, zero_add]
      exact ⟨(mem _).2 (e ▸ hy), e⟩
    · intro u _; simp
    · intro u _; simp
  rw [Finset.card_eq_sum_card_fiberwise (f := L) (t := Y), Finset.sum_congr rfl fib,
    Finset.sum_const, hY, smul_eq_mul]
  intro u hu
  exact (mem u).1 (Finset.mem_filter.mp hu).2

end Split

-- derivatives

section Deriv

variable {n : ℕ}

def D (g : (Fin n → K2) → K2) (a x : Fin n → K2) : K2 := g (x+a) - g x

def D3 (g : (Fin n → K2) → K2) (a b c x : Fin n → K2) : K2 := D (D (D g a) b) c x

lemma D3_expand (g : (Fin n → K2) → K2) (a b c x : Fin n → K2) :
    D3 g a b c x = g (x+c+b+a) - g (x+c+b) - (g (x+c+a) - g (x+c))
      - (g (x+b+a) - g (x+b) - (g (x+a) - g x)) := rfl

lemma D3_swap12 (g : (Fin n → K2) → K2) (a b c x : Fin n → K2) :
    D3 g a b c x = D3 g b a c x := by
  simp only [D3_expand]
  rw [add_right_comm (x+c) b a, add_right_comm x b a]
  ring

lemma D3_swap23 (g : (Fin n → K2) → K2) (a b c x : Fin n → K2) :
    D3 g a b c x = D3 g a c b x := by
  simp only [D3_expand]
  rw [add_right_comm x c b]
  ring

lemma vadd_self (a : Fin n → K2) : a + a = 0 := by
  funext i; exact add_self0 (a i)

lemma D3_alt (g : (Fin n → K2) → K2) (a c x : Fin n → K2) : D3 g a a c x = 0 := by
  have h : ∀ y : Fin n → K2, y + a + a = y := fun y => by rw [add_assoc, vadd_self, add_zero]
  simp only [D3_expand, h]
  ring_nf
  simp [two0]

lemma D3_add (g h : (Fin n → K2) → K2) (a b c x : Fin n → K2) :
    D3 (fun y => g y + h y) a b c x = D3 g a b c x + D3 h a b c x := by
  simp only [D3_expand]; ring

lemma D3_sum {ι : Type} [Fintype ι] (g : ι → (Fin n → K2) → K2) (a b c x : Fin n → K2) :
    D3 (fun y => ∑ i, g i y) a b c x = ∑ i, D3 (g i) a b c x := by
  simp only [D3_expand, Finset.sum_sub_distrib]

lemma D3_prod (p q r a b c x : Fin n → K2) :
    D3 (fun y => dotProduct p y * dotProduct q y * dotProduct r y) a b c x =
      det3 ![dotProduct p a, dotProduct q a, dotProduct r a]
        ![dotProduct p b, dotProduct q b, dotProduct r b]
        ![dotProduct p c, dotProduct q c, dotProduct r c] := by
  simp only [D3_expand, dotProduct_add, det3, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  ring_nf

lemma D3_quad (s : K2) (h : Fin n → K2) (M : Fin n → Fin n → K2) (a b c x : Fin n → K2) :
    D3 (fun x => s + dotProduct h x + ∑ i, ∑ j, M i j * x i * x j) a b c x = 0 := by
  rw [D3_add, D3_add, D3_sum]
  have h1 : D3 (fun _ : Fin n → K2 => s) a b c x = 0 := by simp [D3_expand]
  have h2 : D3 (fun y => dotProduct h y) a b c x = 0 := by
    simp only [D3_expand, dotProduct_add]; ring
  rw [h1, h2, zero_add, zero_add]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [D3_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  simp only [D3_expand, Pi.add_apply]; ring

lemma quad_of_D3 (k : (Fin n → K2) → K2) (hk : ∀ a b c x, D3 k a b c x = 0) :
    ∃ (s : K2) (h : Fin n → K2) (M : Fin n → Fin n → K2),
      ∀ x, k x = s + dotProduct h x + ∑ i, ∑ j, M i j * x i * x j := by
  have second : ∀ a b x : Fin n → K2, D (D k a) b x = D (D k a) b 0 := by
    intro a b x
    have h := hk a b x 0
    unfold D3 at h
    rw [D, zero_add, sub_eq_zero] at h
    exact h
  let S : (Fin n → K2) → (Fin n → K2) → K2 := fun a b => D (D k a) b 0
  have S_ex : ∀ a b, S a b = k (b+a) - k b - (k a - k 0) := by
    intro a b; simp only [S, D, zero_add]
  have S_symm : ∀ a b, S a b = S b a := by
    intro a b; rw [S_ex, S_ex, add_comm a b]; ring
  have S_add : ∀ a b b', S a (b + b') = S a b + S a b' := by
    intro a b b'
    have h := second a b b'
    change D (D k a) b b' = S a b at h
    have e : D (D k a) b b' = S a (b + b') - S a b' := by
      simp only [S_ex, D]
      rw [add_comm b b']
      ring
    rw [e, sub_eq_iff_eq_add] at h
    exact h
  have S_self : ∀ a, S a a = 0 := by
    intro a
    rw [S_ex, vadd_self]
    ring_nf
    simp [two0, CharTwo.sub_eq_add]
  let B : (Fin n → K2) →ₗ[K2] (Fin n → K2) →ₗ[K2] K2 :=
    (AddMonoidHom.mk' (fun a => (AddMonoidHom.mk' (S a) (S_add a)).toZModLinearMap 2)
      (fun a a' => by
        apply LinearMap.ext; intro b
        change S (a + a') b = S a b + S a' b
        rw [S_symm, S_add, S_symm b a, S_symm b a'])).toZModLinearMap 2
  have B_ap : ∀ a b, B a b = S a b := fun _ _ => rfl
  let e : Fin n → (Fin n → K2) := fun i => Pi.single i 1
  let M : Fin n → Fin n → K2 := fun i j => if i < j then S (e i) (e j) else 0
  let q : (Fin n → K2) → K2 := fun x => ∑ i, ∑ j, M i j * x i * x j
  let N : (Fin n → K2) →ₗ[K2] (Fin n → K2) →ₗ[K2] K2 :=
    ∑ i, ∑ j, M i j • ((LinearMap.mul K2 K2).compl₁₂ (LinearMap.proj i) (LinearMap.proj j))
  have N_ap : ∀ x y : Fin n → K2, N x y = ∑ i, ∑ j, M i j * (x i * y j) := by
    intro x y
    simp [N, LinearMap.sum_apply, LinearMap.compl₁₂_apply]
  have q_N : ∀ x, q x = N x x := by
    intro x
    simp only [q, N_ap, mul_assoc]
  have BN : B = N + N.flip := by
    apply (Pi.basisFun K2 (Fin n)).ext
    intro i
    apply (Pi.basisFun K2 (Fin n)).ext
    intro j
    have Ne : ∀ i j, N (e i) (e j) = M i j := by
      intro i j
      rw [N_ap, Finset.sum_eq_single i, Finset.sum_eq_single j]
      · simp [e]
      · intro b _ hb; simp [e, hb]
      · simp
      · intro b _ hb; simp [e, hb]
      · simp
    simp only [Pi.basisFun_apply, LinearMap.add_apply, LinearMap.flip_apply]
    change S (e i) (e j) = N (e i) (e j) + N (e j) (e i)
    rw [Ne, Ne]
    rcases lt_trichotomy i j with h | h | h
    · simp [M, h, not_lt_of_gt h]
    · subst h; simp [M, S_self]
    · simp [M, h, not_lt_of_gt h, S_symm (e i)]
  let r : (Fin n → K2) → K2 := fun x => k x - k 0 - q x
  have r_add : ∀ a b, r (a + b) = r a + r b := by
    intro a b
    have h1 : k (a + b) = S a b + k a + k b - k 0 := by
      rw [S_ex, add_comm b a]; ring
    have h2 : q (a + b) = q a + q b + S a b := by
      rw [q_N, q_N, q_N, ← B_ap, BN]
      simp only [map_add, LinearMap.add_apply, LinearMap.flip_apply]
      ring
    simp only [r, h1, h2]
    ring
  let rl : (Fin n → K2) →ₗ[K2] K2 := (AddMonoidHom.mk' r r_add).toZModLinearMap 2
  refine ⟨k 0, fun i => rl (e i), M, fun x => ?_⟩
  have lin : rl x = dotProduct (fun i => rl (e i)) x := by
    conv_lhs => rw [pi_eq_sum_univ' x]
    rw [map_sum]
    unfold dotProduct
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  rw [← lin]
  change k x = k 0 + (k x - k 0 - q x) + q x
  ring

end Deriv

end PEqualNP.Outside.L_lib_876

open PEqualNP.Outside.L_lib_876 in
set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.L_lib_876 : ∀ n : ℕ,
  let F := ZMod 2
  let V := Fin n → F
  let diff := fun (g : V → F) (a x : V) => g (x+a) - g x
  let third := fun (g : V → F) (a b c : V) => diff (diff (diff g a) b) c 0
  let cubic := fun (g : V → F) => ∀ a b c d x, diff (diff (diff (diff g a) b) c) d x = 0
  let quad := fun (q : V → F) => ∃ (s : F) (h : V) (M : Fin n → Fin n → F),
    ∀ x, q x = s + dotProduct h x + ∑ i, ∑ j, M i j * x i * x j
  let splits := fun (g : V → F) (c : ℕ) =>
    ∃ (A : (Fin c × Fin 3) → V) (q : V → F), LinearIndependent F A ∧ quad q ∧
      ∀ x, g x = q x + ∑ i : Fin c, dotProduct (A (i,0)) x *
        dotProduct (A (i,1)) x * dotProduct (A (i,2)) x
  let unit := fun (i j : Fin n) => if i = j then (1 : F) else 0
  let rankAt := fun (g : V → F) (u : V) =>
    (Matrix.of (fun i j : Fin n => third g u (unit i) (unit j))).rank
  ∀ (g : V → F) (R : Submodule F V), cubic g →
    (∀ u : V, u ∈ R ↔ ∀ v w : V, third g u v w = 0) →
    let d := n - Module.finrank F R
    let good := {u : V | rankAt g u = 2}
    let allDirs := R ⊔ Submodule.span F good = ⊤
    (allDirs ↔ ∃ c : ℕ, d = 3*c ∧ splits g c) ∧
      (allDirs → ((Finset.univ : Finset V).filter (fun u => rankAt g u = 2)).card =
        7 * (d/3) * 2^(Module.finrank F R)) := by
  intro n F V diff third cubic quad splits unit rankAt g R hg hR d good allDirs
  -- the trilinear form
  have th : ∀ a b c, third g a b c = D3 g a b c 0 := fun _ _ _ => rfl
  have const : ∀ a b c x, D3 g a b c x = D3 g a b c 0 := by
    intro a b c x
    have h : D3 g a b c (0 + x) - D3 g a b c 0 = 0 := hg a b c x 0
    rw [zero_add, sub_eq_zero] at h
    exact h
  let t : V → V → V → K2 := fun a b c => D3 g a b c 0
  have t12 : ∀ a b c, t a b c = t b a c := fun a b c => D3_swap12 g a b c 0
  have t23 : ∀ a b c, t a b c = t a c b := fun a b c => D3_swap23 g a b c 0
  have add3 : ∀ a b c c', t a b (c + c') = t a b c + t a b c' := by
    intro a b c c'
    have e : D3 g a b c c' = t a b (c + c') - t a b c' := by
      simp only [t, D3_expand, zero_add]
      rw [add_comm c c']
      ring
    rw [const, sub_eq_add_neg] at e
    change t a b c = t a b (c + c') + -(t a b c') at e
    rw [e]; ring
  have add2 : ∀ a b b' c, t a (b + b') c = t a b c + t a b' c := by
    intro a b b' c
    rw [t23, add3, t23 a c b, t23 a c b']
  have add1 : ∀ a a' b c, t (a + a') b c = t a b c + t a' b c := by
    intro a a' b c
    rw [t12, add2, t12 b a, t12 b a']
  let t3 : V → V → (V →ₗ[K2] K2) := fun a b =>
    (AddMonoidHom.mk' (t a b) (add3 a b)).toZModLinearMap 2
  let t2 : V → (V →ₗ[K2] V →ₗ[K2] K2) := fun a =>
    (AddMonoidHom.mk' (t3 a) (fun b b' => by
      apply LinearMap.ext; intro c; exact add2 a b b' c)).toZModLinearMap 2
  let T : V →ₗ[K2] V →ₗ[K2] V →ₗ[K2] K2 :=
    (AddMonoidHom.mk' t2 (fun a a' => by
      apply LinearMap.ext; intro b; apply LinearMap.ext; intro c
      exact add1 a a' b c)).toZModLinearMap 2
  have T_ap : ∀ a b c, T a b c = D3 g a b c 0 := fun _ _ _ => rfl
  have s1 : ∀ a b c, T a b c = T b a c := t12
  have s2 : ∀ a b c, T a b c = T a c b := t23
  have alt : ∀ a b, T a a b = 0 := fun a b => D3_alt g a b 0
  -- rank two
  have rank_eq : ∀ u : V, rankAt g u = Module.finrank K2 (LinearMap.range (T u)) := by
    intro u
    let eqv := (Pi.basisFun K2 (Fin n)).constr (M' := K2) K2
    have hunit : ∀ i, unit i = Pi.single i (1 : K2) := by
      intro i; funext j
      simp only [unit, Pi.single_apply, eq_comm]
    have key : (Matrix.of (fun i j : Fin n => third g u (unit i) (unit j))).mulVecLin
        = eqv.symm.toLinearMap ∘ₗ (T u) := by
      apply (Pi.basisFun K2 (Fin n)).ext
      intro j
      funext i
      have r : (eqv.symm (T u (Pi.single j 1))) i = T u (Pi.single j 1) (Pi.single i 1) := by
        simp [eqv, Module.Basis.constr_symm_apply]
      simp only [Pi.basisFun_apply, Matrix.mulVecLin_apply, Matrix.mulVec_single_one,
        LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [r, s2]
      change third g u (unit i) (unit j) = T u (Pi.single i 1) (Pi.single j 1)
      rw [hunit, hunit]
      rfl
    change Module.finrank K2 (LinearMap.range
      (Matrix.of (fun i j : Fin n => third g u (unit i) (unit j))).mulVecLin) = _
    rw [key, LinearMap.range_comp]
    exact LinearEquiv.finrank_map_eq eqv.symm _
  have good_rank : ∀ u : V, rankAt g u = 2 ↔ Good T u := by
    intro u
    rw [rank_eq]
    have sym : ∀ a b, T u a b = T u b a := fun a b => s2 u a b
    have self : ∀ a, T u a a = 0 := fun a => by rw [s1, s2]; exact alt a u
    have indep : ∀ a b, T u a b = 1 →
        Module.finrank K2 (Submodule.span K2 (Set.range ![T u a, T u b])) = 2 := by
      intro a b hab
      have hba : T u b a = 1 := by rw [sym]; exact hab
      have li : LinearIndependent K2 ![T u a, T u b] := by
        rw [LinearIndependent.pair_iff]
        intro x y h
        have h1 := LinearMap.congr_fun h a
        have h2 := LinearMap.congr_fun h b
        simp [self, hab, hba] at h1 h2
        exact ⟨h2, h1⟩
      rw [finrank_span_eq_card li, Fintype.card_fin]
    have sub : ∀ a b : V, Submodule.span K2 (Set.range ![T u a, T u b])
        ≤ LinearMap.range (T u) := by
      intro a b
      rw [Submodule.span_le]
      rintro f ⟨i, rfl⟩
      fin_cases i
      · exact ⟨a, rfl⟩
      · exact ⟨b, rfl⟩
    constructor
    · intro h
      have ne : T u ≠ 0 := by
        intro e
        rw [e, LinearMap.range_zero, finrank_bot] at h
        omega
      have ex : ∃ a b, T u a b = 1 := by
        by_contra hno
        apply ne
        apply LinearMap.ext; intro a; apply LinearMap.ext; intro b
        by_contra hne
        exact hno ⟨a, b, ne_zero_one _ hne⟩
      obtain ⟨a, b, hab⟩ := ex
      have hba : T u b a = 1 := by rw [sym]; exact hab
      have eq := Submodule.eq_of_le_of_finrank_eq (sub a b) (by rw [indep a b hab, h])
      refine ⟨a, b, hab, fun x y => ?_⟩
      have hx : T u x ∈ Submodule.span K2 (Set.range ![T u a, T u b]) := by
        rw [eq]; exact ⟨x, rfl⟩
      rw [Submodule.mem_span_range_iff_exists_fun] at hx
      obtain ⟨co, hco⟩ := hx
      rw [Fin.sum_univ_two] at hco
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hco
      have h1 := LinearMap.congr_fun hco a
      have h2 := LinearMap.congr_fun hco b
      have h3 := LinearMap.congr_fun hco y
      simp [self, hab, hba] at h1 h2 h3
      rw [← h3, h1, h2, sym x a, sym x b]
      ring
    · rintro ⟨a, b, hab, h⟩
      have le : LinearMap.range (T u) ≤ Submodule.span K2 (Set.range ![T u a, T u b]) := by
        rintro f ⟨x, rfl⟩
        have e : T u x = (T u a x) • T u b + (T u b x) • T u a := by
          apply LinearMap.ext; intro y
          simpa using h x y
        rw [e]
        exact Submodule.add_mem _
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      rw [le_antisymm le (sub a b), indep a b hab]
  have radR : ∀ u : V, u ∈ R ↔ T u = 0 := by
    intro u
    rw [hR]
    constructor
    · intro h
      apply LinearMap.ext; intro v; apply LinearMap.ext; intro w
      exact h v w
    · intro h v w
      change T u v w = 0
      rw [h]; rfl
  have dirs : allDirs ↔ Submodule.span K2 ({v | Good T v} ∪ {v | T v = 0}) = ⊤ := by
    have e1 : good = {v | Good T v} := by
      ext u; exact good_rank u
    have e2 : ({v | T v = 0} : Set V) = (R : Set V) := by
      ext u; exact (radR u).symm
    change R ⊔ Submodule.span K2 good = ⊤ ↔ _
    rw [e1, e2, Submodule.span_union, Submodule.span_eq, sup_comm]
  -- consequences of a splitting
  have conseq : ∀ (c : ℕ) (L : V →ₗ[K2] (Fin c × Fin 3 → K2)), Function.Surjective L →
      (∀ x y z, T x y z = ∑ i : Fin c, det3 (blk (L x) i) (blk (L y) i) (blk (L z) i)) →
      d = 3 * c ∧ allDirs ∧ ((Finset.univ : Finset V).filter (fun u => rankAt g u = 2)).card =
        7 * (d/3) * 2^(Module.finrank K2 R) := by
    intro c L hL hf
    have RK : R = LinearMap.ker L := by
      ext u
      rw [radR, rad_iff T L hL hf, LinearMap.mem_ker]
    have dim : 3 * c + Module.finrank K2 R = n := by
      have h := L.finrank_range_add_finrank_ker
      rw [LinearMap.range_eq_top.mpr hL, finrank_top, Module.finrank_pi, Module.finrank_pi,
        Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin, ← RK] at h
      omega
    have hd : d = 3 * c := by
      change n - Module.finrank K2 R = 3 * c
      omega
    refine ⟨hd, dirs.2 (span_top T L hL hf), ?_⟩
    classical
    have e : (Finset.univ : Finset V).filter (fun u => rankAt g u = 2)
        = Finset.univ.filter (Good T) :=
      Finset.filter_congr (fun u _ => good_rank u)
    rw [e, good_card T L hL hf, ← RK, hd, Nat.mul_div_cancel_left c (by norm_num), mul_comm c 7]
  -- a splitting of g gives coordinates
  have of_splits : ∀ c, splits g c → ∃ L : V →ₗ[K2] (Fin c × Fin 3 → K2), Function.Surjective L ∧
      (∀ x y z, T x y z = ∑ i : Fin c, det3 (blk (L x) i) (blk (L y) i) (blk (L z) i)) := by
    rintro c ⟨A, q, hA, ⟨s, h, M, hq⟩, hgx⟩
    let Mat : Matrix (Fin c × Fin 3) (Fin n) K2 := Matrix.of A
    let L : V →ₗ[K2] (Fin c × Fin 3 → K2) := Mat.mulVecLin
    have L_ap : ∀ x p, L x p = dotProduct (A p) x := fun _ _ => rfl
    refine ⟨L, ?_, ?_⟩
    · have hr : Mat.rank = Fintype.card (Fin c × Fin 3) := by
        apply LinearIndependent.rank_matrix
        exact hA
      have : LinearMap.range L = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        rw [Module.finrank_pi]
        exact hr
      exact LinearMap.range_eq_top.mp this
    · intro x y z
      have eg : g = fun w => q w + ∑ i : Fin c, dotProduct (A (i,0)) w *
          dotProduct (A (i,1)) w * dotProduct (A (i,2)) w := funext hgx
      have eq : q = fun x => s + dotProduct h x + ∑ i, ∑ j, M i j * x i * x j := funext hq
      rw [T_ap, eg, D3_add, eq, D3_quad, zero_add, D3_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [D3_prod]
      have v3 : ∀ w : V, ![dotProduct (A (i,0)) w, dotProduct (A (i,1)) w,
          dotProduct (A (i,2)) w] = blk (L w) i := by
        intro w
        funext j
        fin_cases j <;> rfl
      rw [v3, v3, v3]
  -- coordinates give a splitting of g
  have to_splits : ∀ (c : ℕ) (L : V →ₗ[K2] (Fin c × Fin 3 → K2)), Function.Surjective L →
      (∀ x y z, T x y z = ∑ i : Fin c, det3 (blk (L x) i) (blk (L y) i) (blk (L z) i)) →
      splits g c := by
    intro c L hL hf
    let A : Fin c × Fin 3 → V := fun p j => L (Pi.single j 1) p
    have Adot : ∀ p x, dotProduct (A p) x = L x p := by
      intro p x
      have e : (LinearMap.proj p ∘ₗ L) x = dotProduct (A p) x := by
        conv_lhs => rw [pi_eq_sum_univ' x]
        rw [map_sum]
        unfold dotProduct
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, smul_eq_mul, mul_comm]
        rfl
      exact e.symm
    let P : V → K2 := fun x => ∑ i : Fin c, dotProduct (A (i,0)) x *
        dotProduct (A (i,1)) x * dotProduct (A (i,2)) x
    have PD : ∀ a b e x, D3 P a b e x = D3 g a b e x := by
      intro a b e x
      rw [const a b e x, ← T_ap, hf]
      simp only [P]
      rw [D3_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [D3_prod]
      have v3 : ∀ w : V, ![dotProduct (A (i,0)) w, dotProduct (A (i,1)) w,
          dotProduct (A (i,2)) w] = blk (L w) i := by
        intro w
        funext j
        fin_cases j <;> exact Adot _ _
      rw [v3, v3, v3]
    refine ⟨A, fun x => g x - P x, ?_, ?_, ?_⟩
    · rw [Fintype.linearIndependent_iff]
      intro co hco p
      obtain ⟨x, hx⟩ := hL (Pi.single p 1)
      have key : ∀ (f : Fin c × Fin 3 → (Fin n → K2)) (x : Fin n → K2),
          dotProduct (∑ i, co i • f i) x = ∑ i, co i * dotProduct (f i) x := by
        intro f x
        rw [sum_dotProduct]
        simp only [smul_dotProduct, smul_eq_mul]
      have e : ∑ i, co i * dotProduct (A i) x = 0 := by
        rw [← key A x]
        have h0 : (∑ i, co i • A i) = (0 : Fin n → K2) := hco
        rw [h0, zero_dotProduct]
      simp only [Adot, hx] at e
      rw [Finset.sum_eq_single p] at e
      · simpa using e
      · intro b _ hb; simp [hb]
      · simp
    · apply quad_of_D3
      intro a b e x
      have : D3 (fun x => g x - P x) a b e x = D3 g a b e x - D3 P a b e x := by
        simp only [D3_expand]; ring
      rw [this, PD, sub_self]
    · intro x
      change g x = g x - P x + P x
      ring
  have forward : allDirs → ∃ (c : ℕ) (L : V →ₗ[K2] (Fin c × Fin 3 → K2)), Function.Surjective L ∧
      (∀ x y z, T x y z = ∑ i : Fin c, det3 (blk (L x) i) (blk (L y) i) (blk (L z) i)) := by
    intro h
    exact splitting _ V T rfl s1 s2 alt (dirs.1 h)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro h
    obtain ⟨c, L, hL, hf⟩ := forward h
    exact ⟨c, (conseq c L hL hf).1, to_splits c L hL hf⟩
  · rintro ⟨c, _, hs⟩
    obtain ⟨L, hL, hf⟩ := of_splits c hs
    exact (conseq c L hL hf).2.1
  · intro h
    obtain ⟨c, L, hL, hf⟩ := forward h
    exact (conseq c L hL hf).2.2
