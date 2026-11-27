import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_590_aux

abbrev V (m : ℕ) := Fin m × Fin 3
abbrev W (m : ℕ) := V m → Bool

def chi {m : ℕ} (S : Finset (V m)) (x : W m) : ZMod 2 :=
  if ∀ a ∈ S, x a = true then 1 else 0

lemma chi_mul {m : ℕ} (S T : Finset (V m)) (x : W m) :
    chi S x * chi T x = chi (S ∪ T) x := by
  unfold chi
  by_cases hS : ∀ a ∈ S, x a = true <;> by_cases hT : ∀ a ∈ T, x a = true
  · have hU : ∀ a ∈ S ∪ T, x a = true := by
      intro a ha; rcases Finset.mem_union.mp ha with h | h
      · exact hS a h
      · exact hT a h
    rw [if_pos hS, if_pos hT, if_pos hU, mul_one]
  · have hU : ¬ ∀ a ∈ S ∪ T, x a = true := fun h => hT (fun a ha => h a (Finset.mem_union_right _ ha))
    rw [if_pos hS, if_neg hT, if_neg hU, mul_zero]
  · have hU : ¬ ∀ a ∈ S ∪ T, x a = true := fun h => hS (fun a ha => h a (Finset.mem_union_left _ ha))
    rw [if_neg hS, if_pos hT, if_neg hU, zero_mul]
  · have hU : ¬ ∀ a ∈ S ∪ T, x a = true := fun h => hS (fun a ha => h a (Finset.mem_union_left _ ha))
    rw [if_neg hS, if_neg hT, if_neg hU, zero_mul]

def evalPoly {m : ℕ} (f : Finset (V m) → ZMod 2) (x : W m) : ZMod 2 :=
  ∑ S : Finset (V m), f S * chi S x

lemma evalPoly_add {m : ℕ} (f g : Finset (V m) → ZMod 2) (x : W m) :
    evalPoly (f + g) x = evalPoly f x + evalPoly g x := by
  simp [evalPoly, add_mul, Finset.sum_add_distrib]

lemma evalPoly_smul {m : ℕ} (c : ZMod 2) (f : Finset (V m) → ZMod 2) (x : W m) :
    evalPoly (c • f) x = c * evalPoly f x := by
  simp [evalPoly, Finset.mul_sum, mul_assoc]

lemma evalPoly_zero {m : ℕ} (x : W m) : evalPoly (0 : Finset (V m) → ZMod 2) x = 0 := by
  simp [evalPoly]

lemma evalPoly_single {m : ℕ} (S : Finset (V m)) (x : W m) :
    evalPoly (fun T => if T = S then 1 else 0) x = chi S x := by
  simp [evalPoly]

lemma evalPoly_injective {m : ℕ} : Function.Injective (@evalPoly m) := by
  intro f g hfg
  have hzero : ∀ x, evalPoly (f - g) x = 0 := by
    intro x
    have : evalPoly (f - g) x = evalPoly f x - evalPoly g x := by
      simp [evalPoly, sub_mul, Finset.sum_sub_distrib]
    rw [this, congrFun hfg x, sub_self]
  by_contra hne
  have hne' : (Finset.univ.filter (fun S : Finset (V m) => (f - g) S ≠ 0)).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    apply hne
    funext S
    have hS : (f - g) S = 0 := by
      by_contra h
      have : S ∈ Finset.univ.filter (fun S : Finset (V m) => (f - g) S ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      rw [hempty] at this; exact Finset.notMem_empty _ this
    exact sub_eq_zero.mp hS
  obtain ⟨S0, hS0mem, hS0min⟩ := Finset.exists_min_image _ Finset.card hne'
  have hS0ne : (f - g) S0 ≠ 0 := (Finset.mem_filter.mp hS0mem).2
  let x0 : W m := fun v => decide (v ∈ S0)
  have hval := hzero x0
  unfold evalPoly at hval
  have hsum : (∑ T : Finset (V m), (f - g) T * chi T x0) = (f - g) S0 := by
    rw [Finset.sum_eq_single S0]
    · have hc : chi S0 x0 = 1 := by simp [chi, x0]
      rw [hc, mul_one]
    · intro T _ hTne
      by_cases hsub : T ⊆ S0
      · have hlt : T.card < S0.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hTne⟩)
        have hTf : (f - g) T = 0 := by
          by_contra h
          have hmem : T ∈ Finset.univ.filter (fun S : Finset (V m) => (f - g) S ≠ 0) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
          have := hS0min T hmem
          omega
        rw [hTf, zero_mul]
      · have hchi : chi T x0 = 0 := by
          unfold chi
          rw [if_neg]
          intro hall
          apply hsub
          intro a ha
          simpa [x0] using hall a ha
        rw [hchi, mul_zero]
    · intro h; exact (h (Finset.mem_univ _)).elim
  rw [hsum] at hval
  exact hS0ne hval

def mulMon {m : ℕ} (T : Finset (V m)) (f : Finset (V m) → ZMod 2) : Finset (V m) → ZMod 2 :=
  fun U => ∑ S ∈ Finset.univ.filter (fun S => T ∪ S = U), f S

lemma evalPoly_mulMon {m : ℕ} (T : Finset (V m)) (f : Finset (V m) → ZMod 2) (x : W m) :
    evalPoly (mulMon T f) x = chi T x * evalPoly f x := by
  unfold evalPoly mulMon
  rw [Finset.mul_sum]
  calc ∑ U : Finset (V m), (∑ S ∈ Finset.univ.filter (fun S => T ∪ S = U), f S) * chi U x
      = ∑ U : Finset (V m), ∑ S ∈ Finset.univ.filter (fun S => T ∪ S = U), f S * chi (T ∪ S) x := by
        refine Finset.sum_congr rfl fun U _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun S hS => ?_
        rw [(Finset.mem_filter.mp hS).2]
    _ = ∑ S : Finset (V m), f S * chi (T ∪ S) x := by
        rw [Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _)]
    _ = ∑ S : Finset (V m), chi T x * (f S * chi S x) := by
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [← chi_mul]; ring

def block {m : ℕ} (i : Fin m) : Finset (V m) :=
  Finset.univ.filter (fun v => v.1 = i)

lemma card_block {m : ℕ} (i : Fin m) : (block i).card = 3 := by
  have heq : block i = {(i, (0 : Fin 3)), (i, (1 : Fin 3)), (i, (2 : Fin 3))} := by
    ext ⟨a, b⟩
    simp only [block, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq]
    fin_cases b <;> tauto
  rw [heq, Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
      Finset.card_singleton]

lemma block_disjoint {m : ℕ} {i j : Fin m} (hij : i ≠ j) : Disjoint (block i) (block j) := by
  rw [Finset.disjoint_left]
  intro v hv1 hv2
  exact hij ((Finset.mem_filter.mp hv1).2.symm.trans (Finset.mem_filter.mp hv2).2)

def ordV {m : ℕ} (i0 : Fin m) (v : V m) : ℕ :=
  if v.1 = i0 then v.2.val else 3 + 3 * v.1.val + v.2.val

lemma ordV_injective {m : ℕ} (i0 : Fin m) : Function.Injective (ordV i0) := by
  intro ⟨a1, b1⟩ ⟨a2, b2⟩ h
  unfold ordV at h
  dsimp only at h
  by_cases h1 : a1 = i0 <;> by_cases h2 : a2 = i0
  · simp only [h1, h2, ↓reduceIte] at h
    exact Prod.ext (h1.trans h2.symm) (Fin.ext h)
  · simp only [h1, h2, ↓reduceIte] at h
    have := b1.isLt; omega
  · simp only [h1, h2, ↓reduceIte] at h
    have := b2.isLt; omega
  · simp only [h1, h2, ↓reduceIte] at h
    have hb1 := b1.isLt; have hb2 := b2.isLt
    have ha : a1.val = a2.val := by omega
    have hb : b1.val = b2.val := by omega
    exact Prod.ext (Fin.ext ha) (Fin.ext hb)

def wt {m : ℕ} (i0 : Fin m) (S : Finset (V m)) : ℕ :=
  ∑ v ∈ S, 2 ^ (ordV i0 v)

lemma wt_union_disjoint {m : ℕ} (i0 : Fin m) {S T : Finset (V m)} (hd : Disjoint S T) :
    wt i0 (S ∪ T) = wt i0 S + wt i0 T :=
  Finset.sum_union hd

lemma sum_pow2_lt (B : Finset ℕ) (k : ℕ) (hB : ∀ j ∈ B, j < k) :
    ∑ j ∈ B, 2 ^ j < 2 ^ k := by
  have hsub : B ⊆ Finset.range k := fun j hj => Finset.mem_range.mpr (hB j hj)
  have hle : ∑ j ∈ B, 2 ^ j ≤ ∑ j ∈ Finset.range k, 2 ^ j :=
    Finset.sum_le_sum_of_subset hsub
  have hgeom : ∀ n : ℕ, ∑ j ∈ Finset.range n, 2 ^ j + 1 = 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, pow_succ]; omega
  have := hgeom k
  omega

lemma wt_injective {m : ℕ} (i0 : Fin m) : Function.Injective (wt i0) := by
  intro S T h
  have himg : S.image (ordV i0) = T.image (ordV i0) := by
    set A := S.image (ordV i0)
    set B := T.image (ordV i0)
    have hsum : ∑ k ∈ A, 2 ^ k = ∑ k ∈ B, 2 ^ k := by
      have hA : wt i0 S = ∑ k ∈ A, 2 ^ k := by
        unfold wt; rw [Finset.sum_image (fun x _ y _ hxy => ordV_injective i0 hxy)]
      have hB : wt i0 T = ∑ k ∈ B, 2 ^ k := by
        unfold wt; rw [Finset.sum_image (fun x _ y _ hxy => ordV_injective i0 hxy)]
      rw [← hA, ← hB, h]
    by_contra hne
    have hdiff : ((A \ B) ∪ (B \ A)).Nonempty := by
      by_contra hempty
      rw [Finset.not_nonempty_iff_eq_empty] at hempty
      apply hne; ext x
      constructor
      · intro hx; by_contra hxB
        have : x ∈ (A \ B) ∪ (B \ A) := Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxB⟩)
        rw [hempty] at this; exact Finset.notMem_empty _ this
      · intro hx; by_contra hxA
        have : x ∈ (A \ B) ∪ (B \ A) := Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx, hxA⟩)
        rw [hempty] at this; exact Finset.notMem_empty _ this
    have hsubEq : ∑ k ∈ A \ B, 2 ^ k = ∑ k ∈ B \ A, 2 ^ k := by
      have hA' : ∑ k ∈ A, 2 ^ k = ∑ k ∈ A \ B, 2 ^ k + ∑ k ∈ A ∩ B, 2 ^ k := by
        have hd : Disjoint (A \ B) (A ∩ B) := by
          rw [Finset.disjoint_left]; intro x h1 h2
          exact (Finset.mem_sdiff.mp h1).2 (Finset.mem_inter.mp h2).2
        have hu : (A \ B) ∪ (A ∩ B) = A := by
          ext x; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
          by_cases hxb : x ∈ B <;> tauto
        rw [← Finset.sum_union hd, hu]
      have hB' : ∑ k ∈ B, 2 ^ k = ∑ k ∈ B \ A, 2 ^ k + ∑ k ∈ A ∩ B, 2 ^ k := by
        have hd : Disjoint (B \ A) (A ∩ B) := by
          rw [Finset.disjoint_left]; intro x h1 h2
          exact (Finset.mem_sdiff.mp h1).2 (Finset.mem_inter.mp h2).1
        have hu : (B \ A) ∪ (A ∩ B) = B := by
          ext x; simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
          by_cases hxa : x ∈ A <;> tauto
        rw [← Finset.sum_union hd, hu]
      omega
    obtain ⟨k, hkMem, hkMax⟩ := Finset.exists_max_image _ id hdiff
    rcases Finset.mem_union.mp hkMem with hkA | hkB
    · have hge : 2 ^ k ≤ ∑ j ∈ A \ B, 2 ^ j :=
        Finset.single_le_sum (f := fun j => 2 ^ j) (fun _ _ => Nat.zero_le _) hkA
      have hlt : ∑ j ∈ B \ A, 2 ^ j < 2 ^ k := sum_pow2_lt (B \ A) k fun j hj => by
        have hle : j ≤ k := hkMax j (Finset.mem_union_right _ hj)
        have hne' : j ≠ k := fun hjk => (Finset.mem_sdiff.mp hj).2 (hjk ▸ (Finset.mem_sdiff.mp hkA).1)
        omega
      omega
    · have hge : 2 ^ k ≤ ∑ j ∈ B \ A, 2 ^ j :=
        Finset.single_le_sum (f := fun j => 2 ^ j) (fun _ _ => Nat.zero_le _) hkB
      have hlt : ∑ j ∈ A \ B, 2 ^ j < 2 ^ k := sum_pow2_lt (A \ B) k fun j hj => by
        have hle : j ≤ k := hkMax j (Finset.mem_union_left _ hj)
        have hne' : j ≠ k := fun hjk => (Finset.mem_sdiff.mp hj).2 (hjk ▸ (Finset.mem_sdiff.mp hkB).1)
        omega
      omega
  ext v
  constructor
  · intro hv
    have : ordV i0 v ∈ T.image (ordV i0) := himg ▸ Finset.mem_image_of_mem _ hv
    obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp this
    exact ordV_injective i0 huv ▸ hu
  · intro hv
    have : ordV i0 v ∈ S.image (ordV i0) := himg.symm ▸ Finset.mem_image_of_mem _ hv
    obtain ⟨u, hu, huv⟩ := Finset.mem_image.mp this
    exact ordV_injective i0 huv ▸ hu

def extCard {m : ℕ} (i0 : Fin m) (S : Finset (V m)) : ℕ :=
  (S.filter (fun v => v.1 ≠ i0)).card

lemma extCard_union_disjoint {m : ℕ} (i0 : Fin m) {S T : Finset (V m)} (hd : Disjoint S T) :
    extCard i0 (S ∪ T) = extCard i0 S + extCard i0 T := by
  unfold extCard
  rw [Finset.filter_union, Finset.card_union_of_disjoint]
  exact Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) hd

-- Key as a lexicographic triple in ℕ ×ₗ ℕ ×ₗ ℕ
abbrev Key := ℕ ×ₗ ℕ ×ₗ ℕ

def keyOf {m : ℕ} (i0 : Fin m) (S : Finset (V m)) : Key :=
  toLex (S.card, toLex (extCard i0 S, wt i0 S))

lemma keyOf_injective {m : ℕ} (i0 : Fin m) : Function.Injective (keyOf i0) := by
  intro S T h
  have h1 : wt i0 S = wt i0 T := by
    have := congrArg (fun k => (ofLex (ofLex k).2).2) h
    exact this
  exact wt_injective i0 h1

lemma keyOf_lt_of_card_lt {m : ℕ} (i0 : Fin m) {S T : Finset (V m)} (h : S.card < T.card) :
    keyOf i0 S < keyOf i0 T :=
  Prod.Lex.left _ _ h

lemma keyOf_lt_of_ext_lt {m : ℕ} (i0 : Fin m) {S T : Finset (V m)}
    (hc : S.card = T.card) (he : extCard i0 S < extCard i0 T) :
    keyOf i0 S < keyOf i0 T := by
  unfold keyOf; rw [hc]; exact Prod.Lex.right _ (Prod.Lex.left _ _ he)

lemma keyOf_lt_of_wt_lt {m : ℕ} (i0 : Fin m) {S T : Finset (V m)}
    (hc : S.card = T.card) (he : extCard i0 S = extCard i0 T) (hw : wt i0 S < wt i0 T) :
    keyOf i0 S < keyOf i0 T := by
  unfold keyOf; rw [hc, he]; exact Prod.Lex.right _ (Prod.Lex.right _ hw)

lemma keyOf_union_lt {m : ℕ} (i0 : Fin m) {T S1 S2 : Finset (V m)}
    (hd2 : Disjoint T S2) (hlt : keyOf i0 S1 < keyOf i0 S2) :
    keyOf i0 (T ∪ S1) < keyOf i0 (T ∪ S2) := by
  have hcard2 : (T ∪ S2).card = T.card + S2.card := Finset.card_union_of_disjoint hd2
  have hlt' : S1.card < S2.card ∨ (S1.card = S2.card ∧
      (extCard i0 S1 < extCard i0 S2 ∨ (extCard i0 S1 = extCard i0 S2 ∧ wt i0 S1 < wt i0 S2))) := by
    unfold keyOf at hlt
    rcases Prod.Lex.lt_iff.mp hlt with hc | ⟨hce, hrest⟩
    · left; exact hc
    · right; refine ⟨hce, ?_⟩
      rcases Prod.Lex.lt_iff.mp hrest with he | ⟨hee, hw⟩
      · left; exact he
      · right; exact ⟨hee, hw⟩
  by_cases hd1 : Disjoint T S1
  · have hcard1 : (T ∪ S1).card = T.card + S1.card := Finset.card_union_of_disjoint hd1
    rcases hlt' with hc | ⟨hce, he | ⟨hee, hw⟩⟩
    · exact keyOf_lt_of_card_lt i0 (by omega)
    · exact keyOf_lt_of_ext_lt i0 (by omega)
        (by rw [extCard_union_disjoint i0 hd1, extCard_union_disjoint i0 hd2]; omega)
    · exact keyOf_lt_of_wt_lt i0 (by omega)
        (by rw [extCard_union_disjoint i0 hd1, extCard_union_disjoint i0 hd2, hee])
        (by rw [wt_union_disjoint i0 hd1, wt_union_disjoint i0 hd2]; omega)
  · have hcard1_lt : (T ∪ S1).card < T.card + S1.card := by
      have hne : (T ∩ S1).Nonempty := Finset.not_disjoint_iff_nonempty_inter.mp hd1
      have hpos : 0 < (T ∩ S1).card := Finset.card_pos.mpr hne
      have := Finset.card_union_add_card_inter T S1
      omega
    have hle : S1.card ≤ S2.card := by
      rcases hlt' with hc | ⟨hce, _⟩ <;> omega
    exact keyOf_lt_of_card_lt i0 (by omega)

lemma keyOf_union_le {m : ℕ} (i0 : Fin m) {T S1 S2 : Finset (V m)}
    (hd2 : Disjoint T S2) (hle : keyOf i0 S1 ≤ keyOf i0 S2) :
    keyOf i0 (T ∪ S1) ≤ keyOf i0 (T ∪ S2) := by
  rcases eq_or_lt_of_le hle with heq | hlt
  · have := keyOf_injective i0 heq; subst this; exact le_rfl
  · exact le_of_lt (keyOf_union_lt i0 hd2 hlt)

def IsLead {m : ℕ} (i0 : Fin m) (f : Finset (V m) → ZMod 2) (S0 : Finset (V m)) : Prop :=
  f S0 = 1 ∧ ∀ S, f S ≠ 0 → keyOf i0 S ≤ keyOf i0 S0

lemma isLead_mulMon {m : ℕ} (i0 : Fin m) {f : Finset (V m) → ZMod 2} {T S0 : Finset (V m)}
    (hl : IsLead i0 f S0) (hd : Disjoint T S0) :
    IsLead i0 (mulMon T f) (T ∪ S0) := by
  refine ⟨?_, ?_⟩
  · unfold mulMon
    rw [Finset.sum_eq_single S0]
    · exact hl.1
    · intro S hSm hSne
      by_contra hnz
      have hle := hl.2 S hnz
      have hlt : keyOf i0 S < keyOf i0 S0 :=
        lt_of_le_of_ne hle (fun heq => hSne (keyOf_injective i0 heq))
      have hult := keyOf_union_lt i0 hd hlt
      rw [(Finset.mem_filter.mp hSm).2] at hult
      exact lt_irrefl _ hult
    · intro h; exact (h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩)).elim
  · intro U hUnz
    unfold mulMon at hUnz
    obtain ⟨S, hSm, hSnz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hUnz
    rw [← (Finset.mem_filter.mp hSm).2]
    exact keyOf_union_le i0 hd (hl.2 S hSnz)

-- Ideal dimension bound: if L is a finset of leading monomials of polynomials vanishing on H,
-- then H.card + L.card ≤ 2^(3*m).
lemma card_add_lead_le {m : ℕ} (i0 : Fin m) (H : Finset (W m)) (L : Finset (Finset (V m)))
    (hL : ∀ S ∈ L, ∃ f : Finset (V m) → ZMod 2, IsLead i0 f S ∧ ∀ x ∈ H, evalPoly f x = 0) :
    H.card + L.card ≤ 2 ^ (3 * m) := by
  classical
  choose g hgLead hgVan using hL
  -- Restriction linear map from (W m → ZMod 2) to (↥H → ZMod 2)
  let res : (W m → ZMod 2) →ₗ[ZMod 2] (↥H → ZMod 2) :=
    { toFun := fun φ x => φ x.1
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hsurj : Function.Surjective res := by
    intro ψ
    refine ⟨fun x => if hx : x ∈ H then ψ ⟨x, hx⟩ else 0, ?_⟩
    funext ⟨x, hx⟩
    simp [res, hx]
  have hrange : Module.finrank (ZMod 2) (LinearMap.range res) = H.card := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_pi, Fintype.card_coe]
  have hdom : Module.finrank (ZMod 2) (W m → ZMod 2) = 2 ^ (3 * m) := by
    rw [Module.finrank_pi, Fintype.card_fun, Fintype.card_bool, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_fin, mul_comm m 3]
  -- Elements in ker res indexed by ↥L
  let vecs : ↥L → LinearMap.ker res := fun S =>
    ⟨evalPoly (g S.1 S.2), by
      rw [LinearMap.mem_ker]
      funext ⟨x, hx⟩
      exact hgVan S.1 S.2 x hx⟩
  have hli : LinearIndependent (ZMod 2) vecs := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    by_contra hne
    push_neg at hne
    let supp := Finset.univ.filter (fun S : ↥L => c S ≠ 0)
    have hneS : supp.Nonempty := by
      obtain ⟨S, hS⟩ := hne
      exact ⟨S, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS⟩⟩
    obtain ⟨Smax, hSmaxMem, hSmax⟩ := Finset.exists_max_image supp (fun S : ↥L => keyOf i0 S.1) hneS
    have hcSmax : c Smax ≠ 0 := (Finset.mem_filter.mp hSmaxMem).2
    -- Combined polynomial has evalPoly = 0, hence polynomial = 0
    let Fcomb : Finset (V m) → ZMod 2 := ∑ S : ↥L, c S • g S.1 S.2
    have heval0 : evalPoly Fcomb = 0 := by
      funext x
      have h1 : evalPoly Fcomb x = ∑ S : ↥L, c S * evalPoly (g S.1 S.2) x := by
        unfold Fcomb evalPoly
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun S _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun T _ => by ring
      rw [h1]
      have h2 := congrArg (fun (v : LinearMap.ker res) => v.1 x) hc
      simp only [Submodule.coe_sum, Submodule.coe_smul_of_tower, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, ZeroMemClass.coe_zero, Pi.zero_apply] at h2
      exact h2
    have hF0 : Fcomb = 0 := evalPoly_injective (by rw [heval0]; funext x; exact (evalPoly_zero x).symm)
    have hcoeff0 : Fcomb Smax.1 = 0 := congrFun hF0 Smax.1
    unfold Fcomb at hcoeff0
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hcoeff0
    rw [Finset.sum_eq_single Smax] at hcoeff0
    · rw [(hgLead Smax.1 Smax.2).1, mul_one] at hcoeff0
      exact hcSmax hcoeff0
    · intro S _ hSne
      by_cases hcS : c S = 0
      · rw [hcS, zero_mul]
      · have hSmem : S ∈ supp := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcS⟩
        have hle := hSmax S hSmem
        have hlt : keyOf i0 S.1 < keyOf i0 Smax.1 :=
          lt_of_le_of_ne hle (fun heq => hSne (Subtype.ext (keyOf_injective i0 heq)))
        have hg0 : g S.1 S.2 Smax.1 = 0 := by
          by_contra hnz
          exact not_le_of_gt hlt ((hgLead S.1 S.2).2 Smax.1 hnz)
        rw [hg0, mul_zero]
    · intro h; exact (h (Finset.mem_univ _)).elim
  have hker : L.card ≤ Module.finrank (ZMod 2) (LinearMap.ker res) := by
    have := hli.fintype_card_le_finrank
    simpa [Fintype.card_coe] using this
  have hrn := LinearMap.finrank_range_add_finrank_ker res
  rw [hrange, hdom] at hrn
  omega

-- Allowed monomials: no block i is contained in S
def Allowed (m : ℕ) : Finset (Finset (V m)) :=
  Finset.univ.filter (fun S => ∀ i : Fin m, ¬ block i ⊆ S)

def Forbidden (m : ℕ) : Finset (Finset (V m)) :=
  Finset.univ.filter (fun S => ∃ i : Fin m, block i ⊆ S)

lemma card_allowed (m : ℕ) : (Allowed m).card = 7 ^ m := by
  classical
  -- Bijection with Fin m → {A : Finset (Fin 3) // A ≠ Finset.univ}
  let Sub3 := {A : Finset (Fin 3) // A ≠ Finset.univ}
  have hcardSub3 : Fintype.card Sub3 = 7 := by decide
  let equiv : ↥(Allowed m) ≃ (Fin m → Sub3) :=
    { toFun := fun ⟨S, hS⟩ i =>
        ⟨(Finset.univ.filter (fun j : Fin 3 => (i, j) ∈ S)), by
          intro heq
          have hsub : block i ⊆ S := by
            intro ⟨a, b⟩ hab
            have ha : a = i := (Finset.mem_filter.mp hab).2
            subst ha
            have hb : b ∈ Finset.univ.filter (fun j : Fin 3 => (a, j) ∈ S) := by
              rw [heq]; exact Finset.mem_univ _
            exact (Finset.mem_filter.mp hb).2
          exact (Finset.mem_filter.mp hS).2 i hsub⟩
      invFun := fun f =>
        ⟨Finset.univ.filter (fun v : V m => v.2 ∈ (f v.1).1), by
          unfold Allowed
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, fun i hsub => (f i).2 ?_⟩
          ext j
          simp only [Finset.mem_univ, iff_true]
          have hmem : (i, j) ∈ block i := by simp [block]
          exact (Finset.mem_filter.mp (hsub hmem)).2⟩
      left_inv := fun ⟨S, hS⟩ => by
        ext ⟨a, b⟩; simp
      right_inv := fun f => by
        funext i; ext j; simp }
  calc (Allowed m).card = Fintype.card ↥(Allowed m) := (Fintype.card_coe _).symm
    _ = Fintype.card (Fin m → Sub3) := Fintype.card_congr equiv
    _ = (Fintype.card Sub3) ^ m := by rw [Fintype.card_fun, Fintype.card_fin]
    _ = 7 ^ m := by rw [hcardSub3]

lemma card_forbidden (m : ℕ) : (Forbidden m).card + 7 ^ m = 2 ^ (3 * m) := by
  have hunion : Forbidden m ∪ Allowed m = Finset.univ := by
    ext S
    simp only [Finset.mem_union, Forbidden, Allowed, Finset.mem_filter, Finset.mem_univ, true_and,
      iff_true]
    by_cases h : ∃ i : Fin m, block i ⊆ S
    · exact Or.inl h
    · push_neg at h; exact Or.inr h
  have hdisj : Disjoint (Forbidden m) (Allowed m) := by
    rw [Finset.disjoint_left]
    intro S hF hA
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hF).2
    exact (Finset.mem_filter.mp hA).2 i hi
  have hc := Finset.card_union_of_disjoint hdisj
  rw [hunion, Finset.card_univ, Fintype.card_finset, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_fin, mul_comm m 3, card_allowed] at hc
  exact hc.symm

-- Helper: count allowed subsets fixing block i0 to a set of options `opts0`,
-- optionally fixing i1 ≠ i0 to `opts1`, optionally fixing i2 ∉ {i0, i1} to `opts2`.
lemma card_allowed_fix1 {m : ℕ} (i0 : Fin m) (opts0 : Finset (Finset (Fin 3)))
    (hopts0 : ∀ A ∈ opts0, A ≠ Finset.univ) :
    ((Allowed m).filter (fun S => (Finset.univ.filter (fun j => (i0, j) ∈ S)) ∈ opts0)).card =
      opts0.card * 7 ^ (m - 1) := by
  classical
  let Sub3 := {A : Finset (Fin 3) // A ≠ Finset.univ}
  have hcardSub3 : Fintype.card Sub3 = 7 := by decide
  let Target := (Allowed m).filter (fun S => (Finset.univ.filter (fun j => (i0, j) ∈ S)) ∈ opts0)
  let equiv : ↥Target ≃ (↥opts0 × ({i : Fin m // i ≠ i0} → Sub3)) :=
    { toFun := fun ⟨S, hS⟩ =>
        let hS' := Finset.mem_filter.mp hS
        (⟨Finset.univ.filter (fun j => (i0, j) ∈ S), hS'.2⟩,
         fun ⟨i, _⟩ => ⟨Finset.univ.filter (fun j => (i, j) ∈ S), by
           intro heq
           have hsub : block i ⊆ S := by
             intro ⟨a, b⟩ hab
             have ha : a = i := (Finset.mem_filter.mp hab).2
             subst ha
             have : b ∈ Finset.univ.filter (fun j => (a, j) ∈ S) := by rw [heq]; exact Finset.mem_univ _
             exact (Finset.mem_filter.mp this).2
           exact (Finset.mem_filter.mp hS'.1).2 i hsub⟩)
      invFun := fun ⟨⟨A0, hA0⟩, g⟩ =>
        ⟨Finset.univ.filter (fun v : V m => if h : v.1 = i0 then v.2 ∈ A0 else v.2 ∈ (g ⟨v.1, h⟩).1), by
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hsub => ?_⟩, ?_⟩
          · by_cases hi : i = i0
            · subst hi
              apply hopts0 A0 hA0
              ext j; simp only [Finset.mem_univ, iff_true]
              have hmem : (i, j) ∈ block i := by simp [block]
              have := (Finset.mem_filter.mp (hsub hmem)).2
              simpa using this
            · apply (g ⟨i, hi⟩).2
              ext j; simp only [Finset.mem_univ, iff_true]
              have hmem : (i, j) ∈ block i := by simp [block]
              have := (Finset.mem_filter.mp (hsub hmem)).2
              simpa [hi] using this
          · have : Finset.univ.filter (fun j => (i0, j) ∈ Finset.univ.filter
                (fun v : V m => if h : v.1 = i0 then v.2 ∈ A0 else v.2 ∈ (g ⟨v.1, h⟩).1)) = A0 := by
              ext j; simp
            rw [this]; exact hA0⟩
      left_inv := fun ⟨S, _⟩ => by
        ext ⟨a, b⟩
        by_cases h : a = i0
        · subst h; simp
        · simp [h]
      right_inv := fun ⟨⟨A0, hA0⟩, g⟩ => by
        apply Prod.ext
        · ext j; simp
        · funext ⟨i, hi⟩; ext j; simp [hi] }
  have hcardNe : Fintype.card {i : Fin m // i ≠ i0} = m - 1 := by
    have := Fintype.card_subtype_compl (fun i : Fin m => i = i0)
    simp only [Fintype.card_unique, Fintype.card_fin] at this
    exact this
  calc Target.card = Fintype.card ↥Target := (Fintype.card_coe _).symm
    _ = Fintype.card (↥opts0 × ({i : Fin m // i ≠ i0} → Sub3)) := Fintype.card_congr equiv
    _ = opts0.card * 7 ^ (m - 1) := by
        rw [Fintype.card_prod, Fintype.card_coe, Fintype.card_fun, hcardSub3, hcardNe]

lemma card_allowed_fix2 {m : ℕ} {i0 i1 : Fin m} (h01 : i0 ≠ i1)
    (opts0 opts1 : Finset (Finset (Fin 3)))
    (hopts0 : ∀ A ∈ opts0, A ≠ Finset.univ) (hopts1 : ∀ A ∈ opts1, A ≠ Finset.univ) :
    ((Allowed m).filter (fun S =>
      (Finset.univ.filter (fun j => (i0, j) ∈ S)) ∈ opts0 ∧
      (Finset.univ.filter (fun j => (i1, j) ∈ S)) ∈ opts1)).card =
      opts0.card * opts1.card * 7 ^ (m - 2) := by
  classical
  let Sub3 := {A : Finset (Fin 3) // A ≠ Finset.univ}
  have hcardSub3 : Fintype.card Sub3 = 7 := by decide
  let Rest := {i : Fin m // i ≠ i0 ∧ i ≠ i1}
  let Target := (Allowed m).filter (fun S =>
    (Finset.univ.filter (fun j => (i0, j) ∈ S)) ∈ opts0 ∧
    (Finset.univ.filter (fun j => (i1, j) ∈ S)) ∈ opts1)
  let equiv : ↥Target ≃ (↥opts0 × ↥opts1 × (Rest → Sub3)) :=
    { toFun := fun ⟨S, hS⟩ =>
        let hS' := Finset.mem_filter.mp hS
        (⟨Finset.univ.filter (fun j => (i0, j) ∈ S), hS'.2.1⟩,
         ⟨Finset.univ.filter (fun j => (i1, j) ∈ S), hS'.2.2⟩,
         fun ⟨i, _⟩ => ⟨Finset.univ.filter (fun j => (i, j) ∈ S), by
           intro heq
           have hsub : block i ⊆ S := by
             intro ⟨a, b⟩ hab
             have ha : a = i := (Finset.mem_filter.mp hab).2
             subst ha
             have : b ∈ Finset.univ.filter (fun j => (a, j) ∈ S) := by rw [heq]; exact Finset.mem_univ _
             exact (Finset.mem_filter.mp this).2
           exact (Finset.mem_filter.mp hS'.1).2 i hsub⟩)
      invFun := fun ⟨⟨A0, hA0⟩, ⟨A1, hA1⟩, g⟩ =>
        ⟨Finset.univ.filter (fun v : V m =>
          if h0 : v.1 = i0 then v.2 ∈ A0
          else if h1 : v.1 = i1 then v.2 ∈ A1
          else v.2 ∈ (g ⟨v.1, h0, h1⟩).1), by
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hsub => ?_⟩, ?_, ?_⟩
          · by_cases hi0 : i = i0
            · subst hi0
              apply hopts0 A0 hA0
              ext j; simp only [Finset.mem_univ, iff_true]
              have hmem : (i, j) ∈ block i := by simp [block]
              have := (Finset.mem_filter.mp (hsub hmem)).2
              simpa using this
            · by_cases hi1 : i = i1
              · subst hi1
                apply hopts1 A1 hA1
                ext j; simp only [Finset.mem_univ, iff_true]
                have hmem : (i, j) ∈ block i := by simp [block]
                have := (Finset.mem_filter.mp (hsub hmem)).2
                simpa [hi0] using this
              · apply (g ⟨i, hi0, hi1⟩).2
                ext j; simp only [Finset.mem_univ, iff_true]
                have hmem : (i, j) ∈ block i := by simp [block]
                have := (Finset.mem_filter.mp (hsub hmem)).2
                simpa [hi0, hi1] using this
          · have : Finset.univ.filter (fun j => (i0, j) ∈ Finset.univ.filter (fun v : V m =>
                if h0 : v.1 = i0 then v.2 ∈ A0 else if h1 : v.1 = i1 then v.2 ∈ A1 else v.2 ∈ (g ⟨v.1, h0, h1⟩).1)) = A0 := by
              ext j; simp
            rw [this]; exact hA0
          · have : Finset.univ.filter (fun j => (i1, j) ∈ Finset.univ.filter (fun v : V m =>
                if h0 : v.1 = i0 then v.2 ∈ A0 else if h1 : v.1 = i1 then v.2 ∈ A1 else v.2 ∈ (g ⟨v.1, h0, h1⟩).1)) = A1 := by
              ext j; simp [h01.symm]
            rw [this]; exact hA1⟩
      left_inv := fun ⟨S, _⟩ => by
        ext ⟨a, b⟩
        by_cases h0 : a = i0
        · subst h0; simp
        · by_cases h1 : a = i1
          · subst h1; simp [h0]
          · simp [h0, h1]
      right_inv := fun ⟨⟨A0, hA0⟩, ⟨A1, hA1⟩, g⟩ => by
        refine Prod.ext ?_ (Prod.ext ?_ ?_)
        · ext j; simp
        · ext j; simp [h01.symm]
        · funext ⟨i, hi0, hi1⟩; ext j; simp [hi0, hi1] }
  have hcardRest : Fintype.card Rest = m - 2 := by
    have hset : (Finset.univ.filter (fun i : Fin m => i ≠ i0 ∧ i ≠ i1)) = (Finset.univ.erase i0).erase i1 := by
      ext i; simp [and_comm]
    have h1 : Fintype.card Rest = (Finset.univ.filter (fun i : Fin m => i ≠ i0 ∧ i ≠ i1)).card :=
      Fintype.card_subtype _
    rw [h1, hset, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ _⟩),
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]
    omega
  calc Target.card = Fintype.card ↥Target := (Fintype.card_coe _).symm
    _ = Fintype.card (↥opts0 × ↥opts1 × (Rest → Sub3)) := Fintype.card_congr equiv
    _ = opts0.card * (opts1.card * 7 ^ (m - 2)) := by
        rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_coe, Fintype.card_coe,
            Fintype.card_fun, hcardSub3, hcardRest]
    _ = opts0.card * opts1.card * 7 ^ (m - 2) := by ring

lemma card_allowed_fix3 {m : ℕ} {i0 i1 i2 : Fin m} (h01 : i0 ≠ i1) (h02 : i0 ≠ i2) (h12 : i1 ≠ i2)
    (opts0 opts1 opts2 : Finset (Finset (Fin 3)))
    (hopts0 : ∀ A ∈ opts0, A ≠ Finset.univ) (hopts1 : ∀ A ∈ opts1, A ≠ Finset.univ)
    (hopts2 : ∀ A ∈ opts2, A ≠ Finset.univ) :
    ((Allowed m).filter (fun S =>
      (Finset.univ.filter (fun j => (i0, j) ∈ S)) ∈ opts0 ∧
      (Finset.univ.filter (fun j => (i1, j) ∈ S)) ∈ opts1 ∧
      (Finset.univ.filter (fun j => (i2, j) ∈ S)) ∈ opts2)).card =
      opts0.card * opts1.card * opts2.card * 7 ^ (m - 3) := by
  classical
  let Sub3 := {A : Finset (Fin 3) // A ≠ Finset.univ}
  have hcardSub3 : Fintype.card Sub3 = 7 := by decide
  let Rest := {i : Fin m // i ≠ i0 ∧ i ≠ i1 ∧ i ≠ i2}
  let Target := (Allowed m).filter (fun S =>
    (Finset.univ.filter (fun j => (i0, j) ∈ S)) ∈ opts0 ∧
    (Finset.univ.filter (fun j => (i1, j) ∈ S)) ∈ opts1 ∧
    (Finset.univ.filter (fun j => (i2, j) ∈ S)) ∈ opts2)
  let equiv : ↥Target ≃ (↥opts0 × ↥opts1 × ↥opts2 × (Rest → Sub3)) :=
    { toFun := fun ⟨S, hS⟩ =>
        let hS' := Finset.mem_filter.mp hS
        (⟨Finset.univ.filter (fun j => (i0, j) ∈ S), hS'.2.1⟩,
         ⟨Finset.univ.filter (fun j => (i1, j) ∈ S), hS'.2.2.1⟩,
         ⟨Finset.univ.filter (fun j => (i2, j) ∈ S), hS'.2.2.2⟩,
         fun ⟨i, _⟩ => ⟨Finset.univ.filter (fun j => (i, j) ∈ S), by
           intro heq
           have hsub : block i ⊆ S := by
             intro ⟨a, b⟩ hab
             have ha : a = i := (Finset.mem_filter.mp hab).2
             subst ha
             have : b ∈ Finset.univ.filter (fun j => (a, j) ∈ S) := by rw [heq]; exact Finset.mem_univ _
             exact (Finset.mem_filter.mp this).2
           exact (Finset.mem_filter.mp hS'.1).2 i hsub⟩)
      invFun := fun ⟨⟨A0, hA0⟩, ⟨A1, hA1⟩, ⟨A2, hA2⟩, g⟩ =>
        ⟨Finset.univ.filter (fun v : V m =>
          if h0 : v.1 = i0 then v.2 ∈ A0
          else if h1 : v.1 = i1 then v.2 ∈ A1
          else if h2 : v.1 = i2 then v.2 ∈ A2
          else v.2 ∈ (g ⟨v.1, h0, h1, h2⟩).1), by
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hsub => ?_⟩, ?_, ?_, ?_⟩
          · by_cases hi0 : i = i0
            · subst hi0; apply hopts0 A0 hA0
              ext j; simp only [Finset.mem_univ, iff_true]
              have hmem : (i, j) ∈ block i := by simp [block]
              simpa using (Finset.mem_filter.mp (hsub hmem)).2
            · by_cases hi1 : i = i1
              · subst hi1; apply hopts1 A1 hA1
                ext j; simp only [Finset.mem_univ, iff_true]
                have hmem : (i, j) ∈ block i := by simp [block]
                simpa [hi0] using (Finset.mem_filter.mp (hsub hmem)).2
              · by_cases hi2 : i = i2
                · subst hi2; apply hopts2 A2 hA2
                  ext j; simp only [Finset.mem_univ, iff_true]
                  have hmem : (i, j) ∈ block i := by simp [block]
                  simpa [hi0, hi1] using (Finset.mem_filter.mp (hsub hmem)).2
                · apply (g ⟨i, hi0, hi1, hi2⟩).2
                  ext j; simp only [Finset.mem_univ, iff_true]
                  have hmem : (i, j) ∈ block i := by simp [block]
                  simpa [hi0, hi1, hi2] using (Finset.mem_filter.mp (hsub hmem)).2
          · have : Finset.univ.filter (fun j => (i0, j) ∈ Finset.univ.filter (fun v : V m =>
                if h0 : v.1 = i0 then v.2 ∈ A0 else if h1 : v.1 = i1 then v.2 ∈ A1 else if h2 : v.1 = i2 then v.2 ∈ A2 else v.2 ∈ (g ⟨v.1, h0, h1, h2⟩).1)) = A0 := by
              ext j; simp
            rw [this]; exact hA0
          · have : Finset.univ.filter (fun j => (i1, j) ∈ Finset.univ.filter (fun v : V m =>
                if h0 : v.1 = i0 then v.2 ∈ A0 else if h1 : v.1 = i1 then v.2 ∈ A1 else if h2 : v.1 = i2 then v.2 ∈ A2 else v.2 ∈ (g ⟨v.1, h0, h1, h2⟩).1)) = A1 := by
              ext j; simp [h01.symm]
            rw [this]; exact hA1
          · have : Finset.univ.filter (fun j => (i2, j) ∈ Finset.univ.filter (fun v : V m =>
                if h0 : v.1 = i0 then v.2 ∈ A0 else if h1 : v.1 = i1 then v.2 ∈ A1 else if h2 : v.1 = i2 then v.2 ∈ A2 else v.2 ∈ (g ⟨v.1, h0, h1, h2⟩).1)) = A2 := by
              ext j; simp [h02.symm, h12.symm]
            rw [this]; exact hA2⟩
      left_inv := fun ⟨S, _⟩ => by
        ext ⟨a, b⟩
        by_cases h0 : a = i0
        · subst h0; simp
        · by_cases h1 : a = i1
          · subst h1; simp [h0]
          · by_cases h2 : a = i2
            · subst h2; simp [h0, h1]
            · simp [h0, h1, h2]
      right_inv := fun ⟨⟨A0, hA0⟩, ⟨A1, hA1⟩, ⟨A2, hA2⟩, g⟩ => by
        refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
        · ext j; simp
        · ext j; simp [h01.symm]
        · ext j; simp [h02.symm, h12.symm]
        · funext ⟨i, hi0, hi1, hi2⟩; ext j; simp [hi0, hi1, hi2] }
  have hcardRest : Fintype.card Rest = m - 3 := by
    have hset : (Finset.univ.filter (fun i : Fin m => i ≠ i0 ∧ i ≠ i1 ∧ i ≠ i2)) =
        ((Finset.univ.erase i0).erase i1).erase i2 := by
      ext i; simp; tauto
    have h1 : Fintype.card Rest = (Finset.univ.filter (fun i : Fin m => i ≠ i0 ∧ i ≠ i1 ∧ i ≠ i2)).card :=
      Fintype.card_subtype _
    rw [h1, hset,
        Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨h12.symm, Finset.mem_erase.mpr ⟨h02.symm, Finset.mem_univ _⟩⟩),
        Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ _⟩),
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]
    omega
  calc Target.card = Fintype.card ↥Target := (Fintype.card_coe _).symm
    _ = Fintype.card (↥opts0 × ↥opts1 × ↥opts2 × (Rest → Sub3)) := Fintype.card_congr equiv
    _ = opts0.card * (opts1.card * (opts2.card * 7 ^ (m - 3))) := by
        rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod,
            Fintype.card_coe, Fintype.card_coe, Fintype.card_coe,
            Fintype.card_fun, hcardSub3, hcardRest]
    _ = opts0.card * opts1.card * opts2.card * 7 ^ (m - 3) := by ring

-- Coordinate flip on W m
def flipW {m : ℕ} (c : V m → Bool) (x : W m) : W m :=
  fun v => xor (x v) (c v)

lemma flipW_invol {m : ℕ} (c : V m → Bool) (x : W m) : flipW c (flipW c x) = x := by
  funext v; unfold flipW; cases x v <;> cases c v <;> rfl

-- Flipping a single monomial chi S (flipW c x) = ∑ T ⊆ S, (if ∀ a ∈ S \ T, c a then 1 else 0) * chi T x
lemma chi_flipW {m : ℕ} (c : V m → Bool) (S : Finset (V m)) (x : W m) :
    chi S (flipW c x) =
      ∑ T ∈ S.powerset, (if ∀ a ∈ S \ T, c a = true then (1 : ZMod 2) else 0) * chi T x := by
  classical
  have hprod : ∀ (A : Finset (V m)),
      chi A (flipW c x) = ∏ a ∈ A, ((if x a then (1 : ZMod 2) else 0) + (if c a then 1 else 0)) := by
    intro A
    induction A using Finset.induction_on with
    | empty => simp [chi]
    | @insert a A ha ih =>
      rw [Finset.prod_insert ha, ← ih]
      have h1 : chi (insert a A) (flipW c x) = chi {a} (flipW c x) * chi A (flipW c x) := by
        rw [chi_mul, Finset.singleton_union]
      rw [h1]; congr 1
      unfold chi flipW
      simp only [Finset.mem_singleton, forall_eq]
      cases x a <;> cases c a <;> decide
  have hprod2 : ∀ (A : Finset (V m)),
      chi A x = ∏ a ∈ A, (if x a then (1 : ZMod 2) else 0) := by
    intro A
    induction A using Finset.induction_on with
    | empty => simp [chi]
    | @insert a A ha ih =>
      rw [Finset.prod_insert ha, ← ih]
      have h1 : chi (insert a A) x = chi {a} x * chi A x := by
        rw [chi_mul, Finset.singleton_union]
      rw [h1]; congr 1
      unfold chi
      simp only [Finset.mem_singleton, forall_eq]
  rw [hprod, Finset.prod_add]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [hprod2, mul_comm]
  congr 1
  by_cases hc : ∀ a ∈ S \ T, c a = true
  · rw [if_pos hc]
    exact Finset.prod_eq_one (fun a ha => by rw [if_pos (hc a ha)])
  · rw [if_neg hc]
    push_neg at hc
    obtain ⟨a, ha, hca⟩ := hc
    have hcf : c a = false := Bool.eq_false_iff.mpr hca
    exact Finset.prod_eq_zero ha (by simp [hcf])

-- Flipping a polynomial Q of degree <= 2 produces a polynomial Q' of degree <= 2
-- preserving all degree-2 coefficients!
lemma flip_low {m : ℕ} (c : V m → Bool) (Q : Finset (V m) → ZMod 2)
    (hQ : ∀ S, Q S ≠ 0 → S.card ≤ 2) :
    ∃ Q' : Finset (V m) → ZMod 2, (∀ S, Q' S ≠ 0 → S.card ≤ 2) ∧
      (∀ T, T.card = 2 → Q' T = Q T) ∧
      ∀ x, evalPoly Q (flipW c x) = evalPoly Q' x := by
  classical
  let Q' : Finset (V m) → ZMod 2 := fun T =>
    ∑ S ∈ Finset.univ.filter (fun S => T ⊆ S),
      Q S * (if ∀ a ∈ S \ T, c a = true then (1 : ZMod 2) else 0)
  refine ⟨Q', ?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨S, hSm, hSnz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hT
    have hQS : Q S ≠ 0 := left_ne_zero_of_mul hSnz
    exact le_trans (Finset.card_le_card (Finset.mem_filter.mp hSm).2) (hQ S hQS)
  · intro T hT2
    dsimp only [Q']
    rw [Finset.sum_eq_single T]
    · simp
    · intro S hSm hST
      have hsub : T ⊆ S := (Finset.mem_filter.mp hSm).2
      have hlt : T.card < S.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hST.symm⟩)
      have hQ0 : Q S = 0 := by
        by_contra hnz
        have := hQ S hnz; omega
      rw [hQ0, zero_mul]
    · intro h; exact (h (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.Subset.rfl⟩)).elim
  · intro x
    unfold evalPoly Q'
    calc ∑ S : Finset (V m), Q S * chi S (flipW c x)
        = ∑ S : Finset (V m), ∑ T ∈ S.powerset,
            Q S * (if ∀ a ∈ S \ T, c a = true then (1 : ZMod 2) else 0) * chi T x := by
          refine Finset.sum_congr rfl fun S _ => ?_
          rw [chi_flipW, Finset.mul_sum]
          refine Finset.sum_congr rfl fun T _ => by ring
      _ = ∑ S : Finset (V m), ∑ T : Finset (V m),
            if T ⊆ S then Q S * (if ∀ a ∈ S \ T, c a = true then (1 : ZMod 2) else 0) * chi T x else 0 := by
          refine Finset.sum_congr rfl fun S _ => ?_
          rw [← Finset.sum_filter]
          congr 1; ext T; simp [Finset.mem_powerset]
      _ = ∑ T : Finset (V m), (∑ S ∈ Finset.univ.filter (fun S => T ⊆ S),
            Q S * (if ∀ a ∈ S \ T, c a = true then (1 : ZMod 2) else 0)) * chi T x := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun T _ => ?_
          rw [Finset.sum_mul, Finset.sum_filter]

-- Flipping a block product chi (block i) produces chi (block i) + R where deg R <= 2
-- and for each j : Fin 3, coeff of (block i).erase (i, j) in R is (if c (i, j) then 1 else 0)!
def blockFlipRem {m : ℕ} (c : V m → Bool) (i : Fin m) : Finset (V m) → ZMod 2 :=
  fun T => if T ⊂ block i then (if ∀ a ∈ block i \ T, c a = true then 1 else 0) else 0

lemma blockFlipRem_deg {m : ℕ} (c : V m → Bool) (i : Fin m) (S : Finset (V m))
    (hS : blockFlipRem c i S ≠ 0) : S.card ≤ 2 := by
  unfold blockFlipRem at hS
  by_cases hss : S ⊂ block i
  · have hlt : S.card < (block i).card := Finset.card_lt_card hss
    rw [card_block] at hlt; omega
  · simp [hss] at hS

lemma blockFlipRem_erase {m : ℕ} (c : V m → Bool) (i : Fin m) (j : Fin 3) :
    blockFlipRem c i ((block i).erase (i, j)) = if c (i, j) then 1 else 0 := by
  have hmem : (i, j) ∈ block i := by simp [block]
  have hss : (block i).erase (i, j) ⊂ block i := Finset.erase_ssubset hmem
  have hsdiff : block i \ (block i).erase (i, j) = {(i, j)} := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_singleton]
    constructor
    · rintro ⟨hv, hne⟩
      by_contra h
      exact hne ⟨h, hv⟩
    · rintro rfl
      exact ⟨hmem, fun h => h.1 rfl⟩
  unfold blockFlipRem
  rw [if_pos hss, hsdiff]
  simp

lemma evalPoly_blockFlipRem {m : ℕ} (c : V m → Bool) (i : Fin m) (x : W m) :
    chi (block i) (flipW c x) = chi (block i) x + evalPoly (blockFlipRem c i) x := by
  classical
  rw [chi_flipW]
  have hmem : block i ∈ (block i).powerset := Finset.mem_powerset.mpr Finset.Subset.rfl
  rw [← Finset.add_sum_erase _ _ hmem]
  have h1 : (if ∀ a ∈ block i \ block i, c a = true then (1 : ZMod 2) else 0) * chi (block i) x =
      chi (block i) x := by simp
  rw [h1]
  congr 1
  unfold evalPoly blockFlipRem
  symm
  rw [← Finset.sum_subset (Finset.subset_univ ((block i).powerset.erase (block i)))]
  · refine Finset.sum_congr rfl fun T hT => ?_
    have hss : T ⊂ block i := by
      have := Finset.mem_erase.mp hT
      exact Finset.ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp this.2, this.1⟩
    rw [if_pos hss]
  · intro T _ hT
    have hnss : ¬ T ⊂ block i := by
      intro hss
      apply hT
      exact Finset.mem_erase.mpr ⟨ne_of_lt hss, Finset.mem_powerset.mpr (le_of_lt hss)⟩
    rw [if_neg hnss, zero_mul]

-- Polynomial (1 + chi {(i0, j)}) * Q
def mulOneAddVar {m : ℕ} (v : V m) (Q : Finset (V m) → ZMod 2) : Finset (V m) → ZMod 2 :=
  Q + mulMon {v} Q

lemma evalPoly_mulOneAddVar {m : ℕ} (v : V m) (Q : Finset (V m) → ZMod 2) (x : W m) :
    evalPoly (mulOneAddVar v Q) x = (1 + chi {v} x) * evalPoly Q x := by
  rw [mulOneAddVar, evalPoly_add, evalPoly_mulMon]; ring

lemma evalPoly_mulOneAddVar_vanish {m : ℕ} {i0 : Fin m} (j : Fin 3)
    {Q : Finset (V m) → ZMod 2} {x : W m} (hx : chi (block i0) x + evalPoly Q x = 0) :
    evalPoly (mulOneAddVar (i0, j) Q) x = 0 := by
  rw [evalPoly_mulOneAddVar]
  have h1 : (1 + chi {(i0, j)} x) * chi (block i0) x = 0 := by
    have hmem : (i0, j) ∈ block i0 := by simp [block]
    unfold chi
    by_cases h : x (i0, j) = true
    · simp only [Finset.mem_singleton, forall_eq, h, ↓reduceIte]
      have : (1 : ZMod 2) + 1 = 0 := by decide
      rw [this, zero_mul]
    · have hb : ¬ ∀ a ∈ block i0, x a = true := fun hall => h (hall _ hmem)
      rw [if_neg hb, mul_zero]
  have hQeq : evalPoly Q x = chi (block i0) x := by
    have h2 : evalPoly Q x + chi (block i0) x = 0 := by rw [add_comm]; exact hx
    have h3 : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
    exact h3 _ _ h2
  rw [hQeq, h1]

-- Explicit coefficient of mulOneAddVar v Q on S:
-- If v ∈ S: Q S + Q S + Q (S.erase v) = Q (S.erase v)!
-- If v ∉ S: Q S!
lemma mulOneAddVar_apply {m : ℕ} (v : V m) (Q : Finset (V m) → ZMod 2) (S : Finset (V m)) :
    mulOneAddVar v Q S = if v ∈ S then Q (S.erase v) else Q S := by
  classical
  unfold mulOneAddVar mulMon
  simp only [Pi.add_apply]
  by_cases hv : v ∈ S
  · rw [if_pos hv]
    have hfilt : Finset.univ.filter (fun T : Finset (V m) => {v} ∪ T = S) = {S, S.erase v} := by
      ext T
      rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      simp only [Finset.mem_univ, true_and, Finset.singleton_union]
      constructor
      · intro h
        by_cases hvT : v ∈ T
        · left; rw [← h, Finset.insert_eq_of_mem hvT]
        · right; rw [← h, Finset.erase_insert hvT]
      · rintro (rfl | rfl)
        · exact Finset.insert_eq_of_mem hv
        · exact Finset.insert_erase hv
    have hne : S ≠ S.erase v := fun h => Finset.notMem_erase v S (h ▸ hv)
    rw [hfilt, Finset.sum_pair hne]
    have h2 : ∀ a b : ZMod 2, a + (a + b) = b := by decide
    exact h2 _ _
  · rw [if_neg hv]
    have hfilt : Finset.univ.filter (fun T : Finset (V m) => {v} ∪ T = S) = ∅ := by
      ext T
      rw [Finset.mem_filter]
      simp only [Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro h
      exact hv (h ▸ Finset.mem_union_left _ (Finset.mem_singleton_self v))
    rw [hfilt, Finset.sum_empty, add_zero]

-- Helper for ZMod 2: f S ≠ 0 ↔ f S = 1
lemma zmod2_ne_zero_iff {a : ZMod 2} : a ≠ 0 ↔ a = 1 := by
  fin_cases a
  · exact ⟨fun h => (h rfl).elim, fun h => (zero_ne_one h).elim⟩
  · exact ⟨fun _ => rfl, fun _ => one_ne_zero⟩

-- Helper: weight of subset of block i0 is <= 7
lemma wt_local_le {m : ℕ} (i0 : Fin m) {A : Finset (V m)} (hA : A ⊆ block i0) :
    wt i0 A ≤ 7 := by
  have hle : wt i0 A ≤ wt i0 (block i0) := Finset.sum_le_sum_of_subset hA
  have hval : wt i0 (block i0) = 7 := by
    have heq : block i0 = {(i0, (0 : Fin 3)), (i0, (1 : Fin 3)), (i0, (2 : Fin 3))} := by
      ext ⟨a, b⟩
      simp only [block, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton, Prod.mk.injEq]
      fin_cases b <;> tauto
    rw [heq, wt]
    have h01 : (i0, (0 : Fin 3)) ≠ (i0, (1 : Fin 3)) := by simp
    have h02 : (i0, (0 : Fin 3)) ≠ (i0, (2 : Fin 3)) := by simp
    have h12 : (i0, (1 : Fin 3)) ≠ (i0, (2 : Fin 3)) := by simp
    rw [Finset.sum_insert (by simp [h01, h02]), Finset.sum_insert (by simp [h12]), Finset.sum_singleton]
    simp [ordV]
  omega

-- Weight comparison: exterior variable w with ordV i0 w' < ordV i0 w beats any local subset + w'
lemma wt_local_add_lt {m : ℕ} (i0 : Fin m) {A B : Finset (V m)} (hA : A ⊆ block i0)
    {w1 w2 : V m} (hw1 : w1.1 ≠ i0) (hw2 : w2.1 ≠ i0) (hlt : ordV i0 w1 < ordV i0 w2) :
    wt i0 (insert w1 A) < wt i0 (insert w2 B) := by
  have h1not : w1 ∉ A := fun hm => hw1 (Finset.mem_filter.mp (hA hm)).2
  have hge3 : 3 ≤ ordV i0 w1 := by simp [ordV, hw1]; omega
  have hpow : 8 ≤ 2 ^ ordV i0 w1 := by
    have : 2 ^ 3 ≤ 2 ^ ordV i0 w1 := Nat.pow_le_pow_right (by norm_num) hge3
    omega
  have hA7 : wt i0 A ≤ 7 := wt_local_le i0 hA
  have hpow2 : 2 ^ (ordV i0 w1 + 1) ≤ 2 ^ ordV i0 w2 := Nat.pow_le_pow_right (by norm_num) hlt
  have hsum1 : wt i0 (insert w1 A) = 2 ^ ordV i0 w1 + wt i0 A := by
    unfold wt; rw [Finset.sum_insert h1not]
  have hsum2 : 2 ^ ordV i0 w2 ≤ wt i0 (insert w2 B) := by
    unfold wt
    exact Finset.single_le_sum (f := fun v => 2 ^ ordV i0 v) (fun _ _ => Nat.zero_le _) (Finset.mem_insert_self w2 B)
  rw [hsum1, pow_succ] at *
  omega

def Hset {m : ℕ} (Q : Fin m → Finset (V m) → ZMod 2) : Finset (W m) :=
  (Finset.univ : Finset (W m)).filter (fun x => ∀ i, chi (block i) x + evalPoly (Q i) x = 0)

lemma upper_finish {m : ℕ} (hm : 2 ≤ m) (Q : Fin m → Finset (V m) → ZMod 2)
    (hdeg : ∀ i S, Q i S ≠ 0 → S.card ≤ 2) (i0 : Fin m)
    (Extra : Finset (Finset (V m))) (hsub : Extra ⊆ Allowed m)
    (hcard : 6 * 7 ^ (m - 2) ≤ Extra.card)
    (hEx : ∀ S ∈ Extra, ∃ f : Finset (V m) → ZMod 2, IsLead i0 f S ∧ ∀ x ∈ Hset Q, evalPoly f x = 0) :
    (Hset Q).card ≤ 43 * 7 ^ (m - 2) := by
  classical
  have hHvan : ∀ i x, x ∈ Hset Q → chi (block i) x + evalPoly (Q i) x = 0 :=
    fun i x hx => (Finset.mem_filter.mp hx).2 i
  have hForb : ∀ S ∈ Forbidden m, ∃ f : Finset (V m) → ZMod 2,
      IsLead i0 f S ∧ ∀ x ∈ Hset Q, evalPoly f x = 0 := by
    intro S hS
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hS).2
    let Fi : Finset (V m) → ZMod 2 := (fun T => if T = block i then 1 else 0) + Q i
    have hFiLead : IsLead i0 Fi (block i) := by
      refine ⟨?_, ?_⟩
      · simp only [Fi, Pi.add_apply, ↓reduceIte]
        have hQ0 : Q i (block i) = 0 := by
          by_contra hnz
          have := hdeg i (block i) hnz
          rw [card_block] at this; omega
        rw [hQ0, add_zero]
      · intro T hT
        by_cases hTb : T = block i
        · rw [hTb]
        · simp only [Fi, Pi.add_apply, if_neg hTb, zero_add] at hT
          have hlt : T.card < (block i).card := by
            have := hdeg i T hT; rw [card_block]; omega
          exact le_of_lt (keyOf_lt_of_card_lt i0 hlt)
    have hFiVan : ∀ x ∈ Hset Q, evalPoly Fi x = 0 := by
      intro x hx
      rw [evalPoly_add, evalPoly_single]
      exact hHvan i x hx
    have hU : (S \ block i) ∪ block i = S := Finset.sdiff_union_of_subset hi
    refine ⟨mulMon (S \ block i) Fi, ?_, ?_⟩
    · have hL := isLead_mulMon (T := S \ block i) i0 hFiLead Finset.sdiff_disjoint
      rwa [hU] at hL
    · intro x hx
      rw [evalPoly_mulMon, hFiVan x hx, mul_zero]
  have hdisj : Disjoint (Forbidden m) Extra := by
    rw [Finset.disjoint_left]
    intro S hF hE
    obtain ⟨i, hi⟩ := (Finset.mem_filter.mp hF).2
    exact (Finset.mem_filter.mp (hsub hE)).2 i hi
  have hbound := card_add_lead_le i0 (Hset Q) (Forbidden m ∪ Extra) (fun S hS => by
    rcases Finset.mem_union.mp hS with h1 | h2
    · exact hForb S h1
    · exact hEx S h2)
  rw [Finset.card_union_of_disjoint hdisj] at hbound
  have hcf := card_forbidden m
  have h7m : 7 ^ m = 49 * 7 ^ (m - 2) := by
    have : m = (m - 2) + 2 := by omega
    conv_lhs => rw [this, pow_add]
    ring
  omega

lemma upper_case1 {m : ℕ} (hm : 2 ≤ m) (Q : Fin m → Finset (V m) → ZMod 2)
    (hdeg : ∀ i S, Q i S ≠ 0 → S.card ≤ 2) (i0 : Fin m)
    (hCase1 : (Finset.univ.filter (fun E : Finset (V m) =>
      Q i0 E ≠ 0 ∧ E.card = 2 ∧ ∀ v ∈ E, v.1 ≠ i0)).Nonempty) :
    (Hset Q).card ≤ 43 * 7 ^ (m - 2) := by
  classical
  set H := Hset Q
  have hHvan : ∀ i x, x ∈ H → chi (block i) x + evalPoly (Q i) x = 0 :=
    fun i x hx => (Finset.mem_filter.mp hx).2 i
  let G : Fin 3 → Finset (V m) → ZMod 2 := fun j => mulOneAddVar (i0, j) (Q i0)
  have hGvan : ∀ j x, x ∈ H → evalPoly (G j) x = 0 :=
    fun j x hx => evalPoly_mulOneAddVar_vanish j (hHvan i0 x hx)
  let extQuad := Finset.univ.filter (fun E : Finset (V m) =>
    Q i0 E ≠ 0 ∧ E.card = 2 ∧ ∀ v ∈ E, v.1 ≠ i0)
  obtain ⟨E, hEmem, hEmax⟩ := Finset.exists_max_image extQuad (keyOf i0) hCase1
  obtain ⟨hQE, hEcard, hEext⟩ := (Finset.mem_filter.mp hEmem).2
  have hQE1 : Q i0 E = 1 := zmod2_ne_zero_iff.mp hQE
  have hEdisj0 : Disjoint E (block i0) := by
    rw [Finset.disjoint_left]
    intro v hvE hv0
    exact hEext v hvE (Finset.mem_filter.mp hv0).2
  -- Every non-empty proper A ⊆ block i0 gives a vanishing polynomial with lead A ∪ E!
  have hAlead : ∀ A : Finset (V m), A ⊆ block i0 → A.Nonempty → A.card ≤ 2 →
      ∃ f : Finset (V m) → ZMod 2, IsLead i0 f (A ∪ E) ∧ ∀ x ∈ H, evalPoly f x = 0 := by
    intro A hAsub hAne hAcard
    obtain ⟨v0, hv0⟩ := hAne
    have hv0eq : v0.1 = i0 := (Finset.mem_filter.mp (hAsub hv0)).2
    let j0 : Fin 3 := v0.2
    have hv0def : v0 = (i0, j0) := Prod.ext hv0eq rfl
    -- First prove IsLead i0 (G j0) (insert (i0, j0) E)
    have hGlead : IsLead i0 (G j0) (insert (i0, j0) E) := by
      have hnotE : (i0, j0) ∉ E := fun hm => hEext _ hm rfl
      have hleadCard : (insert (i0, j0) E).card = 3 := by
        rw [Finset.card_insert_of_notMem hnotE, hEcard]
      have hleadExt : extCard i0 (insert (i0, j0) E) = 2 := by
        unfold extCard
        rw [Finset.filter_insert, if_neg (by simp),
            Finset.filter_true_of_mem (fun v hv => hEext v hv), hEcard]
      refine ⟨?_, ?_⟩
      · dsimp only [G]; rw [mulOneAddVar_apply, if_pos (Finset.mem_insert_self _ _),
            Finset.erase_insert hnotE, hQE1]
      · intro S hSnz
        dsimp only [G] at hSnz; rw [mulOneAddVar_apply] at hSnz
        by_cases hjS : (i0, j0) ∈ S
        · rw [if_pos hjS] at hSnz
          set S' := S.erase (i0, j0)
          have hS'card : S'.card ≤ 2 := hdeg i0 S' hSnz
          have hScard : S.card = S'.card + 1 := (Finset.card_erase_add_one hjS).symm
          by_cases h2 : S'.card = 2
          · have hS3 : S.card = 3 := by omega
            -- Check extCard of S'
            by_cases hall : ∀ v ∈ S', v.1 ≠ i0
            · have hS'mem : S' ∈ extQuad := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSnz, h2, hall⟩
              have hle := hEmax S' hS'mem
              have hSeq : S = {(i0, j0)} ∪ S' := by
                rw [Finset.singleton_union, Finset.insert_erase hjS]
              have hEeq : insert (i0, j0) E = {(i0, j0)} ∪ E := (Finset.singleton_union _ _).symm
              rw [hSeq, hEeq]
              exact keyOf_union_le i0 (Finset.disjoint_singleton_left.mpr hnotE) hle
            · -- S' has at least one local element in block i0, so extCard S <= 1 < 2!
              push_neg at hall
              obtain ⟨u, huS', hui0⟩ := hall
              have hExtLt : extCard i0 S < 2 := by
                have hsub : S.filter (fun v => v.1 ≠ i0) ⊆ S'.erase u := by
                  intro v hv
                  have hv' := Finset.mem_filter.mp hv
                  refine Finset.mem_erase.mpr ⟨fun hvu => hv'.2 (hvu ▸ hui0),
                    Finset.mem_erase.mpr ⟨fun hvj => hv'.2 (hvj ▸ rfl), hv'.1⟩⟩
                have := Finset.card_le_card hsub
                have hcu : (S'.erase u).card = 1 := by rw [Finset.card_erase_of_mem huS', h2]
                unfold extCard; omega
              exact le_of_lt (keyOf_lt_of_ext_lt i0 (by omega) (by omega))
          · exact le_of_lt (keyOf_lt_of_card_lt i0 (by omega))
        · rw [if_neg hjS] at hSnz
          have := hdeg i0 S hSnz
          exact le_of_lt (keyOf_lt_of_card_lt i0 (by omega))
    -- Multiply G j0 by A.erase (i0, j0)!
    have hdisjA : Disjoint (A.erase (i0, j0)) (insert (i0, j0) E) := by
      rw [Finset.disjoint_left]
      intro v hv1 hv2
      have hv1' := Finset.mem_erase.mp hv1
      rcases Finset.mem_insert.mp hv2 with rfl | hvE
      · exact hv1'.1 rfl
      · exact Finset.disjoint_left.mp hEdisj0 hvE (hAsub hv1'.2)
    have hUeq : (A.erase (i0, j0)) ∪ insert (i0, j0) E = A ∪ E := by
      ext v
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_insert]
      by_cases h : v = (i0, j0)
      · subst h; have hmemA : (i0, j0) ∈ A := hv0def ▸ hv0; simp [hmemA]
      · tauto
    refine ⟨mulMon (A.erase (i0, j0)) (G j0), ?_, ?_⟩
    · have hL := isLead_mulMon i0 hGlead hdisjA; rwa [hUeq] at hL
    · intro x hx; rw [evalPoly_mulMon, hGvan j0 x hx, mul_zero]
  -- Now split E = {u1, u2} into same block vs distinct blocks!
  obtain ⟨u1, u2, hu12, hEeq⟩ := Finset.card_eq_two.mp hEcard
  have hu1ext : u1.1 ≠ i0 := hEext u1 (by rw [hEeq]; simp)
  have hu2ext : u2.1 ≠ i0 := hEext u2 (by rw [hEeq]; simp)
  let opts0 : Finset (Finset (Fin 3)) := Finset.univ.filter (fun A => A.Nonempty ∧ A ≠ Finset.univ)
  have hopts0_card : opts0.card = 6 := by decide
  have hopts0_ne : ∀ A ∈ opts0, A ≠ Finset.univ := fun A hA => (Finset.mem_filter.mp hA).2.2
  by_cases hsame : u1.1 = u2.1
  · -- Subcase 1a: u1, u2 in same block i1 ≠ i0
    let i1 := u1.1
    let E1 : Finset (Fin 3) := {u1.2, u2.2}
    have hE1ne : E1 ≠ Finset.univ := by
      intro heq
      have hc := congrArg Finset.card heq
      rw [Finset.card_univ, Fintype.card_fin] at hc
      have : E1.card ≤ 2 := Finset.card_le_two
      omega
    let opts1 : Finset (Finset (Fin 3)) := {E1}
    let Extra := (Allowed m).filter (fun S =>
      (Finset.univ.filter (fun j => (i0, j) ∈ S)) ∈ opts0 ∧
      (Finset.univ.filter (fun j => (i1, j) ∈ S)) ∈ opts1)
    apply upper_finish hm Q hdeg i0 Extra (Finset.filter_subset _ _)
    · rw [card_allowed_fix2 hu1ext.symm opts0 opts1 hopts0_ne (by simp [opts1, hE1ne]),
          hopts0_card, Finset.card_singleton, mul_one]
    · intro S hS
      have hS' := Finset.mem_filter.mp hS
      let A := S.filter (fun v => v.1 = i0)
      have hAsub : A ⊆ block i0 := fun v hv => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩
      have hA3 : Finset.univ.filter (fun j => (i0, j) ∈ S) ∈ opts0 := hS'.2.1
      have hAne : A.Nonempty := by
        obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hA3).2.1
        exact ⟨(i0, j), Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).2, rfl⟩⟩
      have hAcard : A.card ≤ 2 := by
        have hlt : A.card < (block i0).card := Finset.card_lt_card
          (Finset.ssubset_iff_subset_ne.mpr ⟨hAsub, fun heq =>
            (Finset.mem_filter.mp hS'.1).2 i0 (heq ▸ Finset.filter_subset _ _)⟩)
        rw [card_block] at hlt; omega
      have hEsub : E ⊆ S := by
        intro v hv
        rw [hEeq, Finset.mem_insert, Finset.mem_singleton] at hv
        have hS1 : Finset.univ.filter (fun j => (i1, j) ∈ S) = E1 := Finset.mem_singleton.mp hS'.2.2
        rcases hv with hv1 | hv2
        · rw [hv1]
          have : u1.2 ∈ Finset.univ.filter (fun j => (i1, j) ∈ S) := by rw [hS1]; simp [E1]
          exact (Finset.mem_filter.mp this).2
        · rw [hv2]
          have : u2.2 ∈ Finset.univ.filter (fun j => (i1, j) ∈ S) := by rw [hS1]; simp [E1]
          have hmem := (Finset.mem_filter.mp this).2
          rwa [show (i1, u2.2) = u2 from Prod.ext hsame rfl] at hmem
      obtain ⟨f, hfl, hfv⟩ := hAlead A hAsub hAne hAcard
      let T := S \ (A ∪ E)
      have hU : T ∪ (A ∪ E) = S := Finset.sdiff_union_of_subset (Finset.union_subset (Finset.filter_subset _ _) hEsub)
      refine ⟨mulMon T f, ?_, fun x hx => by rw [evalPoly_mulMon, hfv x hx, mul_zero]⟩
      have hL := isLead_mulMon (T := T) i0 hfl Finset.sdiff_disjoint; rwa [hU] at hL
  · -- Subcase 1b: u1.1 ≠ u2.1, both ≠ i0 (so m ≥ 3!)
    let i1 := u1.1; let i2 := u2.1
    have hm3 : 3 ≤ m := by
      have h3 : ({i0, i1, i2} : Finset (Fin m)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [i1, i2, hu1ext.symm, hu2ext.symm]),
            Finset.card_pair hsame]
      have := Finset.card_le_univ ({i0, i1, i2} : Finset (Fin m))
      rw [Fintype.card_fin] at this; omega
    let opts1 : Finset (Finset (Fin 3)) := Finset.univ.filter (fun B => u1.2 ∈ B ∧ B.card ≤ 2)
    let opts2 : Finset (Finset (Fin 3)) := Finset.univ.filter (fun B => u2.2 ∈ B ∧ B.card ≤ 2)
    have hopts_card : ∀ j : Fin 3, (Finset.univ.filter (fun B : Finset (Fin 3) => j ∈ B ∧ B.card ≤ 2)).card = 3 := by
      intro j; fin_cases j <;> decide
    have hopts_ne : ∀ (j : Fin 3) B, B ∈ Finset.univ.filter (fun B : Finset (Fin 3) => j ∈ B ∧ B.card ≤ 2) → B ≠ Finset.univ := by
      intro j B hB heq
      have hc := (Finset.mem_filter.mp hB).2.2
      rw [heq, Finset.card_univ, Fintype.card_fin] at hc; omega
    let Extra := (Allowed m).filter (fun S =>
      (Finset.univ.filter (fun j => (i0, j) ∈ S)) ∈ opts0 ∧
      (Finset.univ.filter (fun j => (i1, j) ∈ S)) ∈ opts1 ∧
      (Finset.univ.filter (fun j => (i2, j) ∈ S)) ∈ opts2)
    apply upper_finish hm Q hdeg i0 Extra (Finset.filter_subset _ _)
    · rw [card_allowed_fix3 hu1ext.symm hu2ext.symm hsame opts0 opts1 opts2
          hopts0_ne (hopts_ne u1.2) (hopts_ne u2.2),
          hopts0_card, hopts_card u1.2, hopts_card u2.2]
      have h7 : 7 ^ (m - 2) = 7 * 7 ^ (m - 3) := by
        have : m - 2 = (m - 3) + 1 := by omega
        rw [this, pow_succ]; ring
      rw [h7]; omega
    · intro S hS
      have hS' := Finset.mem_filter.mp hS
      let A := S.filter (fun v => v.1 = i0)
      have hAsub : A ⊆ block i0 := fun v hv => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩
      have hAne : A.Nonempty := by
        obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hS'.2.1).2.1
        exact ⟨(i0, j), Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).2, rfl⟩⟩
      have hAcard : A.card ≤ 2 := by
        have hlt : A.card < (block i0).card := Finset.card_lt_card
          (Finset.ssubset_iff_subset_ne.mpr ⟨hAsub, fun heq =>
            (Finset.mem_filter.mp hS'.1).2 i0 (heq ▸ Finset.filter_subset _ _)⟩)
        rw [card_block] at hlt; omega
      have hEsub : E ⊆ S := by
        intro v hv
        rw [hEeq, Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl
        · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hS'.2.2.1).2.1).2
        · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hS'.2.2.2).2.1).2
      obtain ⟨f, hfl, hfv⟩ := hAlead A hAsub hAne hAcard
      let T := S \ (A ∪ E)
      have hU : T ∪ (A ∪ E) = S := Finset.sdiff_union_of_subset (Finset.union_subset (Finset.filter_subset _ _) hEsub)
      refine ⟨mulMon T f, ?_, fun x hx => by rw [evalPoly_mulMon, hfv x hx, mul_zero]⟩
      have hL := isLead_mulMon (T := T) i0 hfl Finset.sdiff_disjoint; rwa [hU] at hL

lemma upper_case2 {m : ℕ} (hm : 2 ≤ m) (Q : Fin m → Finset (V m) → ZMod 2)
    (hdeg : ∀ i S, Q i S ≠ 0 → S.card ≤ 2)
    (hnoloc : ∀ i S, Q i S ≠ 0 → S ⊆ block i → S.card ≤ 1)
    (i0 : Fin m)
    (hnoExtQ : ∀ E : Finset (V m), Q i0 E ≠ 0 → E.card = 2 → ∃ v ∈ E, v.1 = i0)
    (hCase2 : (Finset.univ.filter (fun w : V m =>
      w.1 ≠ i0 ∧ ∃ j : Fin 3, Q i0 {(i0, j), w} ≠ 0)).Nonempty) :
    (Hset Q).card ≤ 43 * 7 ^ (m - 2) := by
  classical
  set H := Hset Q
  have hHvan : ∀ i x, x ∈ H → chi (block i) x + evalPoly (Q i) x = 0 :=
    fun i x hx => (Finset.mem_filter.mp hx).2 i
  let G : Fin 3 → Finset (V m) → ZMod 2 := fun j => mulOneAddVar (i0, j) (Q i0)
  have hGvan : ∀ j x, x ∈ H → evalPoly (G j) x = 0 :=
    fun j x hx => evalPoly_mulOneAddVar_vanish j (hHvan i0 x hx)
  let mixExt := Finset.univ.filter (fun w : V m =>
    w.1 ≠ i0 ∧ ∃ j : Fin 3, Q i0 {(i0, j), w} ≠ 0)
  obtain ⟨w, hwMem, hwMax⟩ := Finset.exists_max_image mixExt (ordV i0) hCase2
  obtain ⟨hwExt, jwit, hQjwit⟩ := (Finset.mem_filter.mp hwMem).2
  -- For any j : Fin 3, characterize deg-3 terms of G j!
  have hG3 : ∀ (j : Fin 3) (S : Finset (V m)), G j S ≠ 0 → S.card ≤ 3 := by
    intro j S hSnz
    dsimp only [G] at hSnz; rw [mulOneAddVar_apply] at hSnz
    by_cases hj : (i0, j) ∈ S
    · rw [if_pos hj] at hSnz
      have := hdeg i0 _ hSnz
      have := Finset.card_erase_add_one hj
      omega
    · rw [if_neg hj] at hSnz
      have := hdeg i0 _ hSnz; omega
  -- Every deg-3 term of G j has the form {(i0, j), (i0, k), w'} with k ≠ j, w'.1 ≠ i0, ordV w' ≤ ordV w!
  have hG3form : ∀ (j : Fin 3) (S : Finset (V m)), G j S ≠ 0 → S.card = 3 →
      ∃ (k : Fin 3) (w' : V m), k ≠ j ∧ w'.1 ≠ i0 ∧ S = {(i0, j), (i0, k), w'} ∧
        Q i0 {(i0, k), w'} ≠ 0 ∧ ordV i0 w' ≤ ordV i0 w := by
    intro j S hSnz hS3
    dsimp only [G] at hSnz; rw [mulOneAddVar_apply] at hSnz
    by_cases hj : (i0, j) ∈ S
    · rw [if_pos hj] at hSnz
      set S' := S.erase (i0, j)
      have hS'2 : S'.card = 2 := by have : S'.card + 1 = S.card := Finset.card_erase_add_one hj; omega
      obtain ⟨u, huS', hui0⟩ := hnoExtQ S' hSnz hS'2
      have hnotSub : ¬ S' ⊆ block i0 := fun hsub => by
        have := hnoloc i0 S' hSnz hsub; omega
      obtain ⟨w', hw'S', hw'not⟩ := Finset.not_subset.mp hnotSub
      have hw'ext : w'.1 ≠ i0 := fun h => hw'not (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
      have huw' : u ≠ w' := fun h => hw'ext (h ▸ hui0)
      have hS'eq : S' = {u, w'} := by
        refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
        · intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx2
          · exact huS'
          · rw [Finset.mem_singleton.mp hx2]; exact hw'S'
        · rw [Finset.card_pair huw', hS'2]
      have huEq : u = (i0, u.2) := Prod.ext hui0 rfl
      have hkj : u.2 ≠ j := fun h =>
        Finset.notMem_erase (i0, j) S (show (i0, j) ∈ S' from by rw [← h, ← huEq]; exact huS')
      have hS'eq2 : S' = {(i0, u.2), w'} := by rw [← huEq]; exact hS'eq
      have hSeq : S = {(i0, j), (i0, u.2), w'} := by
        rw [← Finset.insert_erase hj]; exact congrArg (insert (i0, j)) hS'eq2
      have hw'le : ordV i0 w' ≤ ordV i0 w :=
        hwMax w' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw'ext, u.2, hS'eq2 ▸ hSnz⟩)
      exact ⟨u.2, w', hkj, hw'ext, hSeq, hS'eq2 ▸ hSnz, hw'le⟩
    · rw [if_neg hj] at hSnz
      have := hdeg i0 S hSnz; omega
  -- Compare any deg-3 term {(i0,j),(i0,k),w'} of G j against {(i0,j),(i0,k0),w}:
  have hkeyPair : ∀ (j k0 : Fin 3) (hj : k0 ≠ j)
      (hval : Q i0 {(i0, k0), w} = 1)
      (hmaxk : ∀ k : Fin 3, k ≠ j → Q i0 {(i0, k), w} ≠ 0 → k.val ≤ k0.val),
      IsLead i0 (G j) {(i0, j), (i0, k0), w} := by
    intro j k0 hkj hval hmaxk
    have hnot1 : (i0, j) ∉ ({(i0, k0), w} : Finset (V m)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hkj (congrArg Prod.snd h).symm, fun h => hwExt (congrArg Prod.fst h).symm⟩
    refine ⟨?_, ?_⟩
    · dsimp only [G]; rw [mulOneAddVar_apply, if_pos (Finset.mem_insert_self _ _),
          Finset.erase_insert hnot1, hval]
    · intro S hSnz
      have hSc := hG3 j S hSnz
      have hT3 : ({(i0, j), (i0, k0), w} : Finset (V m)).card = 3 := by
        rw [Finset.card_insert_of_notMem hnot1,
            Finset.card_pair (fun h => hwExt (congrArg Prod.fst h).symm)]
      by_cases h3 : S.card = 3
      · obtain ⟨k, w', hkj', hw'ext, rfl, hQk, hw'le⟩ := hG3form j S hSnz h3
        have hExt1 : extCard i0 ({(i0, j), (i0, k), w'} : Finset (V m)) = 1 := by
          unfold extCard
          rw [Finset.filter_insert, if_neg (by simp), Finset.filter_insert, if_neg (by simp),
              Finset.filter_singleton, if_pos hw'ext, Finset.card_singleton]
        have hExt2 : extCard i0 ({(i0, j), (i0, k0), w} : Finset (V m)) = 1 := by
          unfold extCard
          rw [Finset.filter_insert, if_neg (by simp), Finset.filter_insert, if_neg (by simp),
              Finset.filter_singleton, if_pos hwExt, Finset.card_singleton]
        rcases eq_or_lt_of_le hw'le with hweq | hwlt
        · have hwEq : w' = w := ordV_injective i0 hweq
          subst w'
          have hkle : k.val ≤ k0.val := hmaxk k hkj' hQk
          rcases eq_or_lt_of_le hkle with hkeq | hklt
          · have hkEq : k = k0 := Fin.ext hkeq; subst hkEq; exact le_rfl
          · apply le_of_lt
            apply keyOf_lt_of_wt_lt i0 (by rw [h3, hT3]) (by rw [hExt1, hExt2])
            -- Compare weights of {(i0,j),(i0,k),w} < {(i0,j),(i0,k0),w}
            have hwt : ∀ a : Fin 3, a ≠ j →
                wt i0 ({(i0, j), (i0, a), w} : Finset (V m)) = 2 ^ j.val + 2 ^ a.val + 2 ^ ordV i0 w := by
              intro a haj
              unfold wt
              have hne1 : (i0, j) ∉ ({(i0, a), w} : Finset (V m)) := by
                simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
                exact ⟨fun h => haj (congrArg Prod.snd h).symm, fun h => hwExt (congrArg Prod.fst h).symm⟩
              have hne2 : (i0, a) ∉ ({w} : Finset (V m)) := by
                simp only [Finset.mem_singleton]
                exact fun h => hwExt (congrArg Prod.fst h).symm
              rw [Finset.sum_insert hne1, Finset.sum_insert hne2, Finset.sum_singleton]
              simp [ordV]; ring
            rw [hwt k hkj', hwt k0 hkj]
            have := Nat.pow_lt_pow_right (by norm_num : 1 < 2) hklt
            omega
        · apply le_of_lt
          apply keyOf_lt_of_wt_lt i0 (by rw [h3, hT3]) (by rw [hExt1, hExt2])
          have hS' : ({(i0, j), (i0, k), w'} : Finset (V m)) = insert w' {(i0, j), (i0, k)} := by
            ext x; simp; tauto
          have hT' : ({(i0, j), (i0, k0), w} : Finset (V m)) = insert w {(i0, j), (i0, k0)} := by
            ext x; simp; tauto
          rw [hS', hT']
          exact wt_local_add_lt i0 (fun v hv => by
            simp only [Finset.mem_insert, Finset.mem_singleton] at hv
            rcases hv with rfl | rfl <;> simp [block]) hw'ext hwExt hwlt
      · exact le_of_lt (keyOf_lt_of_card_lt i0 (by omega))
  -- Now find TWO DISTINCT pairs P1, P2 : Finset (Fin 3) of size 2 with lead (P1_v ∪ {w}) and (P2_v ∪ {w})!
  let b0 := decide (Q i0 {(i0, 0), w} ≠ 0)
  let b1 := decide (Q i0 {(i0, 1), w} ≠ 0)
  let b2 := decide (Q i0 {(i0, 2), w} ≠ 0)
  have hb_or : b0 = true ∨ b1 = true ∨ b2 = true := by
    fin_cases jwit
    · left; simpa [b0] using hQjwit
    · right; left; simpa [b1] using hQjwit
    · right; right; simpa [b2] using hQjwit
  have hTwoPairs : ∃ (P1 P2 : Finset (Fin 3)), P1 ≠ P2 ∧ P1.card = 2 ∧ P2.card = 2 ∧
      (∃ j1, IsLead i0 (G j1) (insert w (P1.image (fun a => (i0, a))))) ∧
      (∃ j2, IsLead i0 (G j2) (insert w (P2.image (fun a => (i0, a))))) := by
    have hmk : ∀ (j k : Fin 3), ({(i0, j), (i0, k), w} : Finset (V m)) =
        insert w (({j, k} : Finset (Fin 3)).image (fun a => (i0, a))) := by
      intro j k; ext x; simp; tauto
    have hq : ∀ a : Fin 3, (if a = 0 then b0 else if a = 1 then b1 else b2) = true ↔ Q i0 {(i0, a), w} ≠ 0 := by
      intro a; fin_cases a <;> simp [b0, b1, b2]
    have hq1 : ∀ a : Fin 3, (if a = 0 then b0 else if a = 1 then b1 else b2) = true → Q i0 {(i0, a), w} = 1 :=
      fun a ha => zmod2_ne_zero_iff.mp ((hq a).mp ha)
    -- Case split on (b0, b1, b2) ∈ Bool^3 \ {(false,false,false)}
    cases hb0 : b0 <;> cases hb1 : b1 <;> cases hb2 : b2
    · simp [hb0, hb1, hb2] at hb_or
    · -- (F, F, T): G 0 leads {0,2}, G 1 leads {1,2}
      refine ⟨{0, 2}, {1, 2}, by decide, by decide, by decide,
        ⟨0, hmk 0 2 ▸ hkeyPair 0 2 (by decide) (hq1 2 (by simp [hb2])) (fun k hkj hk => by
          fin_cases k
          · exact (hkj rfl).elim
          · have := (hq 1).mpr hk; simp [hb1] at this
          · decide)⟩,
        ⟨1, hmk 1 2 ▸ hkeyPair 1 2 (by decide) (hq1 2 (by simp [hb2])) (fun k hkj hk => by
          fin_cases k
          · have := (hq 0).mpr hk; simp [hb0] at this
          · exact (hkj rfl).elim
          · decide)⟩⟩
    · -- (F, T, F): G 0 leads {0,1}, G 2 leads {2,1}
      refine ⟨{0, 1}, {2, 1}, by decide, by decide, by decide,
        ⟨0, hmk 0 1 ▸ hkeyPair 0 1 (by decide) (hq1 1 (by simp [hb1])) (fun k hkj hk => by
          fin_cases k
          · exact (hkj rfl).elim
          · decide
          · have := (hq 2).mpr hk; simp [hb2] at this)⟩,
        ⟨2, hmk 2 1 ▸ hkeyPair 2 1 (by decide) (hq1 1 (by simp [hb1])) (fun k hkj hk => by
          fin_cases k
          · have := (hq 0).mpr hk; simp [hb0] at this
          · decide
          · exact (hkj rfl).elim)⟩⟩
    · -- (F, T, T): G 0 leads {0,2}, G 1 leads {1,2}
      refine ⟨{0, 2}, {1, 2}, by decide, by decide, by decide,
        ⟨0, hmk 0 2 ▸ hkeyPair 0 2 (by decide) (hq1 2 (by simp [hb2])) (fun k _ _ => by fin_cases k <;> decide)⟩,
        ⟨1, hmk 1 2 ▸ hkeyPair 1 2 (by decide) (hq1 2 (by simp [hb2])) (fun k _ _ => by fin_cases k <;> decide)⟩⟩
    · -- (T, F, F): G 1 leads {1,0}, G 2 leads {2,0}
      refine ⟨{1, 0}, {2, 0}, by decide, by decide, by decide,
        ⟨1, hmk 1 0 ▸ hkeyPair 1 0 (by decide) (hq1 0 (by simp [hb0])) (fun k hkj hk => by
          fin_cases k
          · decide
          · exact (hkj rfl).elim
          · have := (hq 2).mpr hk; simp [hb2] at this)⟩,
        ⟨2, hmk 2 0 ▸ hkeyPair 2 0 (by decide) (hq1 0 (by simp [hb0])) (fun k hkj hk => by
          fin_cases k
          · decide
          · have := (hq 1).mpr hk; simp [hb1] at this
          · exact (hkj rfl).elim)⟩⟩
    · -- (T, F, T): G 0 leads {0,2}, G 1 leads {1,2}
      refine ⟨{0, 2}, {1, 2}, by decide, by decide, by decide,
        ⟨0, hmk 0 2 ▸ hkeyPair 0 2 (by decide) (hq1 2 (by simp [hb2])) (fun k _ _ => by fin_cases k <;> decide)⟩,
        ⟨1, hmk 1 2 ▸ hkeyPair 1 2 (by decide) (hq1 2 (by simp [hb2])) (fun k _ _ => by fin_cases k <;> decide)⟩⟩
    · -- (T, T, F): G 0 leads {0,1}, G 2 leads {2,1}
      refine ⟨{0, 1}, {2, 1}, by decide, by decide, by decide,
        ⟨0, hmk 0 1 ▸ hkeyPair 0 1 (by decide) (hq1 1 (by simp [hb1])) (fun k hkj hk => by
          fin_cases k
          · exact (hkj rfl).elim
          · decide
          · have := (hq 2).mpr hk; simp [hb2] at this)⟩,
        ⟨2, hmk 2 1 ▸ hkeyPair 2 1 (by decide) (hq1 1 (by simp [hb1])) (fun k hkj hk => by
          fin_cases k
          · decide
          · decide
          · exact (hkj rfl).elim)⟩⟩
    · -- (T, T, T): G 0 leads {0,2}, G 1 leads {1,2}
      refine ⟨{0, 2}, {1, 2}, by decide, by decide, by decide,
        ⟨0, hmk 0 2 ▸ hkeyPair 0 2 (by decide) (hq1 2 (by simp [hb2])) (fun k _ _ => by fin_cases k <;> decide)⟩,
        ⟨1, hmk 1 2 ▸ hkeyPair 1 2 (by decide) (hq1 2 (by simp [hb2])) (fun k _ _ => by fin_cases k <;> decide)⟩⟩
  obtain ⟨P1, P2, hPne, hP1c, hP2c, ⟨j1, hL1⟩, ⟨j2, hL2⟩⟩ := hTwoPairs
  let opts0 : Finset (Finset (Fin 3)) := {P1, P2}
  let opts1 : Finset (Finset (Fin 3)) := Finset.univ.filter (fun B => w.2 ∈ B ∧ B.card ≤ 2)
  have hopts0_ne : ∀ A ∈ opts0, A ≠ Finset.univ := by
    intro A hA heq
    have hc : A.card = 2 := by
      rcases Finset.mem_insert.mp hA with rfl | hA2
      · exact hP1c
      · rw [Finset.mem_singleton.mp hA2]; exact hP2c
    rw [heq, Finset.card_univ, Fintype.card_fin] at hc; omega
  have hopts1_card : opts1.card = 3 := by
    have : ∀ j : Fin 3, (Finset.univ.filter (fun B : Finset (Fin 3) => j ∈ B ∧ B.card ≤ 2)).card = 3 := by
      intro j; fin_cases j <;> decide
    exact this w.2
  have hopts1_ne : ∀ B ∈ opts1, B ≠ Finset.univ := by
    intro B hB heq
    have hc := (Finset.mem_filter.mp hB).2.2
    rw [heq, Finset.card_univ, Fintype.card_fin] at hc; omega
  let Extra := (Allowed m).filter (fun S =>
    (Finset.univ.filter (fun j => (i0, j) ∈ S)) ∈ opts0 ∧
    (Finset.univ.filter (fun j => (w.1, j) ∈ S)) ∈ opts1)
  apply upper_finish hm Q hdeg i0 Extra (Finset.filter_subset _ _)
  · rw [card_allowed_fix2 hwExt.symm opts0 opts1 hopts0_ne hopts1_ne,
        Finset.card_pair hPne, hopts1_card]
  · intro S hS
    have hS' := Finset.mem_filter.mp hS
    have hwS : w ∈ S := (Finset.mem_filter.mp (Finset.mem_filter.mp hS'.2.2).2.1).2
    rcases Finset.mem_insert.mp hS'.2.1 with hS0 | hS0'
    · have hsub : insert w (P1.image (fun a => (i0, a))) ⊆ S := by
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv2
        · exact hwS
        · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv2
          rw [← hS0] at ha; exact (Finset.mem_filter.mp ha).2
      let T := S \ insert w (P1.image (fun a => (i0, a)))
      have hU : T ∪ insert w (P1.image (fun a => (i0, a))) = S := Finset.sdiff_union_of_subset hsub
      refine ⟨mulMon T (G j1), ?_, fun x hx => by rw [evalPoly_mulMon, hGvan j1 x hx, mul_zero]⟩
      have hL := isLead_mulMon (T := T) i0 hL1 Finset.sdiff_disjoint; rwa [hU] at hL
    · have hS0 := Finset.mem_singleton.mp hS0'
      have hsub : insert w (P2.image (fun a => (i0, a))) ⊆ S := by
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv2
        · exact hwS
        · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv2
          rw [← hS0] at ha; exact (Finset.mem_filter.mp ha).2
      let T := S \ insert w (P2.image (fun a => (i0, a)))
      have hU : T ∪ insert w (P2.image (fun a => (i0, a))) = S := Finset.sdiff_union_of_subset hsub
      refine ⟨mulMon T (G j2), ?_, fun x hx => by rw [evalPoly_mulMon, hGvan j2 x hx, mul_zero]⟩
      have hL := isLead_mulMon (T := T) i0 hL2 Finset.sdiff_disjoint; rwa [hU] at hL

lemma upper_case3a {m : ℕ} (hm : 2 ≤ m) (Q : Fin m → Finset (V m) → ZMod 2)
    (hdeg : ∀ i S, Q i S ≠ 0 → S.card ≤ 2) (i0 : Fin m)
    (hdeg1 : ∀ S, Q i0 S ≠ 0 → S.card ≤ 1)
    (hCase3a : (Finset.univ.filter (fun w : V m => w.1 ≠ i0 ∧ Q i0 {w} ≠ 0)).Nonempty) :
    (Hset Q).card ≤ 43 * 7 ^ (m - 2) := by
  classical
  set H := Hset Q
  have hHvan : ∀ i x, x ∈ H → chi (block i) x + evalPoly (Q i) x = 0 :=
    fun i x hx => (Finset.mem_filter.mp hx).2 i
  let G : Fin 3 → Finset (V m) → ZMod 2 := fun j => mulOneAddVar (i0, j) (Q i0)
  have hGvan : ∀ j x, x ∈ H → evalPoly (G j) x = 0 :=
    fun j x hx => evalPoly_mulOneAddVar_vanish j (hHvan i0 x hx)
  let extLin := Finset.univ.filter (fun w : V m => w.1 ≠ i0 ∧ Q i0 {w} ≠ 0)
  obtain ⟨w, hwMem, hwMax⟩ := Finset.exists_max_image extLin (ordV i0) hCase3a
  obtain ⟨hwExt, hQw⟩ := (Finset.mem_filter.mp hwMem).2
  have hQw1 : Q i0 {w} = 1 := zmod2_ne_zero_iff.mp hQw
  have hGlead : ∀ j : Fin 3, IsLead i0 (G j) {(i0, j), w} := by
    intro j
    have hjw : (i0, j) ≠ w := fun h => hwExt (congrArg Prod.fst h).symm
    have hT2 : ({(i0, j), w} : Finset (V m)).card = 2 := Finset.card_pair hjw
    have hExtT : extCard i0 ({(i0, j), w} : Finset (V m)) = 1 := by
      unfold extCard
      rw [Finset.filter_insert, if_neg (by simp), Finset.filter_singleton, if_pos hwExt, Finset.card_singleton]
    refine ⟨?_, ?_⟩
    · dsimp only [G]; rw [mulOneAddVar_apply, if_pos (Finset.mem_insert_self _ _),
          Finset.erase_insert (by simp [hjw]), hQw1]
    · intro S hSnz
      dsimp only [G] at hSnz; rw [mulOneAddVar_apply] at hSnz
      by_cases hj : (i0, j) ∈ S
      · rw [if_pos hj] at hSnz
        set S' := S.erase (i0, j)
        have hS'1 := hdeg1 S' hSnz
        have hSc : S.card = S'.card + 1 := (Finset.card_erase_add_one hj).symm
        by_cases h1 : S'.card = 1
        · obtain ⟨w', hS'eq⟩ := Finset.card_eq_one.mp h1
          have hSeq : S = {(i0, j), w'} := by rw [← Finset.insert_erase hj]; exact congrArg (insert (i0, j)) hS'eq
          by_cases hw'ext : w'.1 ≠ i0
          · have hw'le : ordV i0 w' ≤ ordV i0 w :=
              hwMax w' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw'ext, hS'eq ▸ hSnz⟩)
            rcases eq_or_lt_of_le hw'le with hweq | hwlt
            · have := ordV_injective i0 hweq; subst this; rw [hSeq]
            · apply le_of_lt
              have hExtS : extCard i0 S = 1 := by
                rw [hSeq]; unfold extCard
                rw [Finset.filter_insert, if_neg (by simp), Finset.filter_singleton, if_pos hw'ext, Finset.card_singleton]
              apply keyOf_lt_of_wt_lt i0 (by omega) (by rw [hExtS, hExtT])
              rw [hSeq]
              have hS' : ({(i0, j), w'} : Finset (V m)) = insert w' {(i0, j)} := Finset.pair_comm _ _
              have hT' : ({(i0, j), w} : Finset (V m)) = insert w {(i0, j)} := Finset.pair_comm _ _
              rw [hS', hT']
              exact wt_local_add_lt i0 (fun v hv => by rw [Finset.mem_singleton.mp hv]; simp [block]) hw'ext hwExt hwlt
          · push_neg at hw'ext
            have hExt0 : extCard i0 S = 0 := by
              rw [hSeq]; unfold extCard
              rw [Finset.filter_insert, if_neg (by simp), Finset.filter_singleton, if_neg (by simp [hw'ext]), Finset.card_empty]
            exact le_of_lt (keyOf_lt_of_ext_lt i0 (by omega) (by omega))
        · exact le_of_lt (keyOf_lt_of_card_lt i0 (by omega))
      · rw [if_neg hj] at hSnz
        have := hdeg1 S hSnz
        exact le_of_lt (keyOf_lt_of_card_lt i0 (by omega))
  let opts0 : Finset (Finset (Fin 3)) := {{0}, {1}, {2}}
  let opts1 : Finset (Finset (Fin 3)) := Finset.univ.filter (fun B => w.2 ∈ B ∧ B.card ≤ 2)
  have hopts0_card : opts0.card = 3 := by decide
  have hopts0_ne : ∀ A ∈ opts0, A ≠ Finset.univ := by decide
  have hopts1_card : opts1.card = 3 := by
    have : ∀ j : Fin 3, (Finset.univ.filter (fun B : Finset (Fin 3) => j ∈ B ∧ B.card ≤ 2)).card = 3 := by
      intro j; fin_cases j <;> decide
    exact this w.2
  have hopts1_ne : ∀ B ∈ opts1, B ≠ Finset.univ := by
    intro B hB heq; have hc := (Finset.mem_filter.mp hB).2.2
    rw [heq, Finset.card_univ, Fintype.card_fin] at hc; omega
  let Extra := (Allowed m).filter (fun S =>
    (Finset.univ.filter (fun j => (i0, j) ∈ S)) ∈ opts0 ∧
    (Finset.univ.filter (fun j => (w.1, j) ∈ S)) ∈ opts1)
  apply upper_finish hm Q hdeg i0 Extra (Finset.filter_subset _ _)
  · rw [card_allowed_fix2 hwExt.symm opts0 opts1 hopts0_ne hopts1_ne, hopts0_card, hopts1_card]
    omega
  · intro S hS
    have hS' := Finset.mem_filter.mp hS
    have hwS : w ∈ S := (Finset.mem_filter.mp (Finset.mem_filter.mp hS'.2.2).2.1).2
    have hA : Finset.univ.filter (fun j => (i0, j) ∈ S) ∈ opts0 := hS'.2.1
    have hexj : ∃ j : Fin 3, (i0, j) ∈ S := by
      rcases Finset.mem_insert.mp hA with h0 | h12
      · have hm0 : (0 : Fin 3) ∈ Finset.univ.filter (fun j => (i0, j) ∈ S) := by rw [h0]; simp
        exact ⟨0, (Finset.mem_filter.mp hm0).2⟩
      · rcases Finset.mem_insert.mp h12 with h1 | h2
        · have hm1 : (1 : Fin 3) ∈ Finset.univ.filter (fun j => (i0, j) ∈ S) := by rw [h1]; simp
          exact ⟨1, (Finset.mem_filter.mp hm1).2⟩
        · have h2' : Finset.univ.filter (fun j => (i0, j) ∈ S) = {2} := Finset.mem_singleton.mp h2
          have hm2 : (2 : Fin 3) ∈ Finset.univ.filter (fun j => (i0, j) ∈ S) := by rw [h2']; simp
          exact ⟨2, (Finset.mem_filter.mp hm2).2⟩
    obtain ⟨j, hjS⟩ := hexj
    have hsub : ({(i0, j), w} : Finset (V m)) ⊆ S := by
      intro v hv; rcases Finset.mem_insert.mp hv with rfl | hv2
      · exact hjS
      · rw [Finset.mem_singleton.mp hv2]; exact hwS
    let T := S \ {(i0, j), w}
    have hU : T ∪ {(i0, j), w} = S := Finset.sdiff_union_of_subset hsub
    refine ⟨mulMon T (G j), ?_, fun x hx => by rw [evalPoly_mulMon, hGvan j x hx, mul_zero]⟩
    have hL := isLead_mulMon (T := T) i0 (hGlead j) Finset.sdiff_disjoint; rwa [hU] at hL

lemma upper_case3b {m : ℕ} (hm : 2 ≤ m) (Q : Fin m → Finset (V m) → ZMod 2)
    (hdeg : ∀ i S, Q i S ≠ 0 → S.card ≤ 2) (i0 : Fin m) (hQne : Q i0 ≠ 0)
    (hdeg1 : ∀ S, Q i0 S ≠ 0 → S.card ≤ 1)
    (hCase3a : ¬ (Finset.univ.filter (fun w : V m => w.1 ≠ i0 ∧ Q i0 {w} ≠ 0)).Nonempty) :
    (Hset Q).card ≤ 43 * 7 ^ (m - 2) := by
  classical
  set H := Hset Q
  have hHvan : ∀ i x, x ∈ H → chi (block i) x + evalPoly (Q i) x = 0 :=
    fun i x hx => (Finset.mem_filter.mp hx).2 i
  let G : Fin 3 → Finset (V m) → ZMod 2 := fun j => mulOneAddVar (i0, j) (Q i0)
  have hGvan : ∀ j x, x ∈ H → evalPoly (G j) x = 0 :=
    fun j x hx => evalPoly_mulOneAddVar_vanish j (hHvan i0 x hx)
  have hlocOnly : ∀ S, Q i0 S ≠ 0 → S ⊆ block i0 := by
    intro S hSnz
    have h1 := hdeg1 S hSnz
    by_cases h0 : S = ∅
    · rw [h0]; exact Finset.empty_subset _
    · have hc : S.card = 1 := by
        have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr h0); omega
      obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hc
      by_cases hv : v.1 = i0
      · intro x hx; rw [Finset.mem_singleton.mp hx]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
      · exact (hCase3a ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv, hSnz⟩⟩).elim
  -- Check whether any local linear term Q i0 {(i0, k)} ≠ 0 exists!
  let b0 := decide (Q i0 {(i0, 0)} ≠ 0)
  let b1 := decide (Q i0 {(i0, 1)} ≠ 0)
  let b2 := decide (Q i0 {(i0, 2)} ≠ 0)
  have hTwoLocal : ∃ (P1 P2 : Finset (Fin 3)), P1 ≠ P2 ∧ P1 ≠ Finset.univ ∧ P2 ≠ Finset.univ ∧
      (∃ j1, IsLead i0 (G j1) (P1.image (fun a => (i0, a)))) ∧
      (∃ j2, IsLead i0 (G j2) (P2.image (fun a => (i0, a)))) := by
    by_cases hallF : b0 = false ∧ b1 = false ∧ b2 = false
    · -- Only constant term Q i0 ∅ = 1! Then G 0 leads {(i0,0)} and G 1 leads {(i0,1)}!
      have hQ0 : Q i0 ∅ = 1 := by
        by_contra hne
        apply hQne
        funext S
        by_contra hSnz
        have h1 := hdeg1 S hSnz
        have hsub := hlocOnly S hSnz
        by_cases hSe : S = ∅
        · subst hSe; exact hne (zmod2_ne_zero_iff.mp hSnz)
        · have hc : S.card = 1 := by
            have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hSe); omega
          obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hc
          have hv : v.1 = i0 := (Finset.mem_filter.mp (hsub (Finset.mem_singleton_self v))).2
          have hvEq : v = (i0, v.2) := Prod.ext hv rfl
          rw [hvEq] at hSnz
          rcases v with ⟨va, vb⟩; dsimp only at hvEq hSnz; fin_cases vb
          · have h0' : Q i0 {(i0, 0)} ≠ 0 := hSnz; simp [b0, h0'] at hallF
          · have h1' : Q i0 {(i0, 1)} ≠ 0 := hSnz; simp [b1, h1'] at hallF
          · have h2' : Q i0 {(i0, 2)} ≠ 0 := hSnz; simp [b2, h2'] at hallF
      have hGconst : ∀ j : Fin 3, IsLead i0 (G j) {(i0, j)} := by
        intro j
        refine ⟨?_, ?_⟩
        · dsimp only [G]; rw [mulOneAddVar_apply, if_pos (Finset.mem_singleton_self _),
              Finset.erase_singleton, hQ0]
        · intro S hSnz
          dsimp only [G] at hSnz; rw [mulOneAddVar_apply] at hSnz
          by_cases hj : (i0, j) ∈ S
          · rw [if_pos hj] at hSnz
            have hSe : S.erase (i0, j) = ∅ := by
              by_contra hne
              have h1 := hdeg1 _ hSnz
              have hsub := hlocOnly _ hSnz
              have hc : (S.erase (i0, j)).card = 1 := by
                have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne); omega
              obtain ⟨v, hvEq⟩ := Finset.card_eq_one.mp hc
              have hv : v.1 = i0 := (Finset.mem_filter.mp (hsub (by rw [hvEq]; simp))).2
              have hv' : v = (i0, v.2) := Prod.ext hv rfl
              rw [hvEq, hv'] at hSnz
              rcases v with ⟨va, vb⟩; dsimp only at hv' hSnz; fin_cases vb
              · have h0' : Q i0 {(i0, 0)} ≠ 0 := hSnz; simp [b0, h0'] at hallF
              · have h1' : Q i0 {(i0, 1)} ≠ 0 := hSnz; simp [b1, h1'] at hallF
              · have h2' : Q i0 {(i0, 2)} ≠ 0 := hSnz; simp [b2, h2'] at hallF
            have : S = {(i0, j)} := by rw [← Finset.insert_erase hj, hSe]; simp
            rw [this]
          · rw [if_neg hj] at hSnz
            have hSe : S = ∅ := by
              by_contra hne
              have h1 := hdeg1 _ hSnz
              have hsub := hlocOnly _ hSnz
              have hc : S.card = 1 := by
                have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne); omega
              obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hc
              have hv : v.1 = i0 := (Finset.mem_filter.mp (hsub (Finset.mem_singleton_self v))).2
              have hv' : v = (i0, v.2) := Prod.ext hv rfl
              rw [hv'] at hSnz
              rcases v with ⟨va, vb⟩; dsimp only at hv' hSnz; fin_cases vb
              · have h0' : Q i0 {(i0, 0)} ≠ 0 := hSnz; simp [b0, h0'] at hallF
              · have h1' : Q i0 {(i0, 1)} ≠ 0 := hSnz; simp [b1, h1'] at hallF
              · have h2' : Q i0 {(i0, 2)} ≠ 0 := hSnz; simp [b2, h2'] at hallF
            rw [hSe]; exact le_of_lt (keyOf_lt_of_card_lt i0 (by simp))
      refine ⟨{0}, {1}, by decide, by decide, by decide,
        ⟨0, by simpa using hGconst 0⟩, ⟨1, by simpa using hGconst 1⟩⟩
    · -- Some local linear term exists! Same 7-case lemma as Case 2!
      have hkeyLoc : ∀ (j k0 : Fin 3) (hkj : k0 ≠ j) (hval : Q i0 {(i0, k0)} = 1)
          (hmaxk : ∀ k : Fin 3, k ≠ j → Q i0 {(i0, k)} ≠ 0 → k.val ≤ k0.val),
          IsLead i0 (G j) {(i0, j), (i0, k0)} := by
        intro j k0 hkj hval hmaxk
        have hjk : (i0, j) ≠ (i0, k0) := fun h => hkj (congrArg Prod.snd h).symm
        refine ⟨?_, ?_⟩
        · dsimp only [G]; rw [mulOneAddVar_apply, if_pos (Finset.mem_insert_self _ _),
              Finset.erase_insert (by simp [hjk]), hval]
        · intro S hSnz
          dsimp only [G] at hSnz; rw [mulOneAddVar_apply] at hSnz
          by_cases hj : (i0, j) ∈ S
          · rw [if_pos hj] at hSnz
            set S' := S.erase (i0, j)
            have h1 := hdeg1 S' hSnz
            have hsub := hlocOnly S' hSnz
            have hSc : S.card = S'.card + 1 := (Finset.card_erase_add_one hj).symm
            by_cases h1eq : S'.card = 1
            · obtain ⟨v, hvEq⟩ := Finset.card_eq_one.mp h1eq
              have hv : v.1 = i0 := (Finset.mem_filter.mp (hsub (by rw [hvEq]; simp))).2
              have hv' : v = (i0, v.2) := Prod.ext hv rfl
              have hkj' : v.2 ≠ j := fun h =>
                Finset.notMem_erase (i0, j) S (show (i0, j) ∈ S' from by rw [hvEq, hv', h]; simp)
              have hSeq : S = {(i0, j), (i0, v.2)} := by rw [← Finset.insert_erase hj]; exact congrArg (insert (i0, j)) (hvEq.trans (congrArg (fun x => ({x} : Finset (V m))) hv'))
              have hkle := hmaxk v.2 hkj' (by rw [hvEq, hv'] at hSnz; exact hSnz)
              rcases eq_or_lt_of_le hkle with hkeq | hklt
              · have : v.2 = k0 := Fin.ext hkeq; rw [hSeq, this]
              · apply le_of_lt
                have hT2 : ({(i0, j), (i0, k0)} : Finset (V m)).card = 2 := Finset.card_pair hjk
                have hExt0 : ∀ a : Fin 3, extCard i0 ({(i0, j), (i0, a)} : Finset (V m)) = 0 := by
                  intro a; unfold extCard
                  rw [Finset.filter_insert, if_neg (by simp), Finset.filter_singleton, if_neg (by simp), Finset.card_empty]
                rw [hSeq]
                apply keyOf_lt_of_wt_lt i0 (by rw [Finset.card_pair (fun h => hkj' (congrArg Prod.snd h).symm), hT2]) (by rw [hExt0, hExt0])
                have hwt : ∀ a : Fin 3, a ≠ j → wt i0 ({(i0, j), (i0, a)} : Finset (V m)) = 2 ^ j.val + 2 ^ a.val := by
                  intro a haj; unfold wt
                  rw [Finset.sum_pair (fun h => haj (congrArg Prod.snd h).symm)]; simp [ordV]
                rw [hwt v.2 hkj', hwt k0 hkj]
                have := Nat.pow_lt_pow_right (by norm_num : 1 < 2) hklt
                omega
            · exact le_of_lt (keyOf_lt_of_card_lt i0 (by rw [Finset.card_pair hjk]; omega))
          · rw [if_neg hj] at hSnz
            have := hdeg1 S hSnz
            exact le_of_lt (keyOf_lt_of_card_lt i0 (by rw [Finset.card_pair hjk]; omega))
      have hmk : ∀ (j k : Fin 3), ({(i0, j), (i0, k)} : Finset (V m)) =
          ({j, k} : Finset (Fin 3)).image (fun a => (i0, a)) := by
        intro j k; ext x; simp
      have hq : ∀ a : Fin 3, (if a = 0 then b0 else if a = 1 then b1 else b2) = true ↔ Q i0 {(i0, a)} ≠ 0 := by
        intro a; fin_cases a <;> simp [b0, b1, b2]
      have hq1 : ∀ a : Fin 3, (if a = 0 then b0 else if a = 1 then b1 else b2) = true → Q i0 {(i0, a)} = 1 :=
        fun a ha => zmod2_ne_zero_iff.mp ((hq a).mp ha)
      cases hb0 : b0 <;> cases hb1 : b1 <;> cases hb2 : b2
      · exact (hallF ⟨hb0, hb1, hb2⟩).elim
      · refine ⟨{0, 2}, {1, 2}, by decide, by decide, by decide,
          ⟨0, hmk 0 2 ▸ hkeyLoc 0 2 (by decide) (hq1 2 (by simp [hb2])) (fun k hkj hk => by
            fin_cases k
            · exact (hkj rfl).elim
            · have := (hq 1).mpr hk; simp [hb1] at this
            · decide)⟩,
          ⟨1, hmk 1 2 ▸ hkeyLoc 1 2 (by decide) (hq1 2 (by simp [hb2])) (fun k hkj hk => by
            fin_cases k
            · have := (hq 0).mpr hk; simp [hb0] at this
            · exact (hkj rfl).elim
            · decide)⟩⟩
      · refine ⟨{0, 1}, {2, 1}, by decide, by decide, by decide,
          ⟨0, hmk 0 1 ▸ hkeyLoc 0 1 (by decide) (hq1 1 (by simp [hb1])) (fun k hkj hk => by
            fin_cases k
            · exact (hkj rfl).elim
            · decide
            · have := (hq 2).mpr hk; simp [hb2] at this)⟩,
          ⟨2, hmk 2 1 ▸ hkeyLoc 2 1 (by decide) (hq1 1 (by simp [hb1])) (fun k hkj hk => by
            fin_cases k
            · have := (hq 0).mpr hk; simp [hb0] at this
            · decide
            · exact (hkj rfl).elim)⟩⟩
      · refine ⟨{0, 2}, {1, 2}, by decide, by decide, by decide,
          ⟨0, hmk 0 2 ▸ hkeyLoc 0 2 (by decide) (hq1 2 (by simp [hb2])) (fun k _ _ => by fin_cases k <;> decide)⟩,
          ⟨1, hmk 1 2 ▸ hkeyLoc 1 2 (by decide) (hq1 2 (by simp [hb2])) (fun k _ _ => by fin_cases k <;> decide)⟩⟩
      · refine ⟨{1, 0}, {2, 0}, by decide, by decide, by decide,
          ⟨1, hmk 1 0 ▸ hkeyLoc 1 0 (by decide) (hq1 0 (by simp [hb0])) (fun k hkj hk => by
            fin_cases k
            · decide
            · exact (hkj rfl).elim
            · have := (hq 2).mpr hk; simp [hb2] at this)⟩,
          ⟨2, hmk 2 0 ▸ hkeyLoc 2 0 (by decide) (hq1 0 (by simp [hb0])) (fun k hkj hk => by
            fin_cases k
            · decide
            · have := (hq 1).mpr hk; simp [hb1] at this
            · exact (hkj rfl).elim)⟩⟩
      · refine ⟨{0, 2}, {1, 2}, by decide, by decide, by decide,
          ⟨0, hmk 0 2 ▸ hkeyLoc 0 2 (by decide) (hq1 2 (by simp [hb2])) (fun k _ _ => by fin_cases k <;> decide)⟩,
          ⟨1, hmk 1 2 ▸ hkeyLoc 1 2 (by decide) (hq1 2 (by simp [hb2])) (fun k _ _ => by fin_cases k <;> decide)⟩⟩
      · refine ⟨{0, 1}, {2, 1}, by decide, by decide, by decide,
          ⟨0, hmk 0 1 ▸ hkeyLoc 0 1 (by decide) (hq1 1 (by simp [hb1])) (fun k hkj hk => by
            fin_cases k
            · exact (hkj rfl).elim
            · decide
            · have := (hq 2).mpr hk; simp [hb2] at this)⟩,
          ⟨2, hmk 2 1 ▸ hkeyLoc 2 1 (by decide) (hq1 1 (by simp [hb1])) (fun k hkj hk => by
            fin_cases k
            · decide
            · decide
            · exact (hkj rfl).elim)⟩⟩
      · refine ⟨{0, 2}, {1, 2}, by decide, by decide, by decide,
          ⟨0, hmk 0 2 ▸ hkeyLoc 0 2 (by decide) (hq1 2 (by simp [hb2])) (fun k _ _ => by fin_cases k <;> decide)⟩,
          ⟨1, hmk 1 2 ▸ hkeyLoc 1 2 (by decide) (hq1 2 (by simp [hb2])) (fun k _ _ => by fin_cases k <;> decide)⟩⟩
  obtain ⟨P1, P2, hPne, hP1u, hP2u, ⟨j1, hL1⟩, ⟨j2, hL2⟩⟩ := hTwoLocal
  let opts0 : Finset (Finset (Fin 3)) := {P1, P2}
  have hopts0_ne : ∀ A ∈ opts0, A ≠ Finset.univ := by
    intro A hA; rcases Finset.mem_insert.mp hA with rfl | hA2
    · exact hP1u
    · rw [Finset.mem_singleton.mp hA2]; exact hP2u
  let Extra := (Allowed m).filter (fun S => (Finset.univ.filter (fun j => (i0, j) ∈ S)) ∈ opts0)
  apply upper_finish hm Q hdeg i0 Extra (Finset.filter_subset _ _)
  · rw [card_allowed_fix1 i0 opts0 hopts0_ne, Finset.card_pair hPne]
    have h7 : 7 ^ (m - 1) = 7 * 7 ^ (m - 2) := by
      have : m - 1 = (m - 2) + 1 := by omega
      rw [this, pow_succ]; ring
    rw [h7]; omega
  · intro S hS
    have hS' := Finset.mem_filter.mp hS
    rcases Finset.mem_insert.mp hS'.2 with hS0 | hS0'
    · have hsub : P1.image (fun a => (i0, a)) ⊆ S := by
        intro v hv; obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
        rw [← hS0] at ha; exact (Finset.mem_filter.mp ha).2
      let T := S \ P1.image (fun a => (i0, a))
      have hU : T ∪ P1.image (fun a => (i0, a)) = S := Finset.sdiff_union_of_subset hsub
      refine ⟨mulMon T (G j1), ?_, fun x hx => by rw [evalPoly_mulMon, hGvan j1 x hx, mul_zero]⟩
      have hL := isLead_mulMon (T := T) i0 hL1 Finset.sdiff_disjoint; rwa [hU] at hL
    · have hS0 := Finset.mem_singleton.mp hS0'
      have hsub : P2.image (fun a => (i0, a)) ⊆ S := by
        intro v hv; obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hv
        rw [← hS0] at ha; exact (Finset.mem_filter.mp ha).2
      let T := S \ P2.image (fun a => (i0, a))
      have hU : T ∪ P2.image (fun a => (i0, a)) = S := Finset.sdiff_union_of_subset hsub
      refine ⟨mulMon T (G j2), ?_, fun x hx => by rw [evalPoly_mulMon, hGvan j2 x hx, mul_zero]⟩
      have hL := isLead_mulMon (T := T) i0 hL2 Finset.sdiff_disjoint; rwa [hU] at hL


lemma upper_normalized {m : ℕ} (hm : 2 ≤ m) (Q : Fin m → Finset (V m) → ZMod 2)
    (hdeg : ∀ i S, Q i S ≠ 0 → S.card ≤ 2)
    (hnoloc : ∀ i S, Q i S ≠ 0 → S ⊆ block i → S.card ≤ 1)
    (i0 : Fin m) (hQne : Q i0 ≠ 0) :
    ((Finset.univ : Finset (W m)).filter (fun x => ∀ i, chi (block i) x + evalPoly (Q i) x = 0)).card ≤
      43 * 7 ^ (m - 2) := by
  classical
  change (Hset Q).card ≤ 43 * 7 ^ (m - 2)
  let extQuad := Finset.univ.filter (fun E : Finset (V m) =>
    Q i0 E ≠ 0 ∧ E.card = 2 ∧ ∀ v ∈ E, v.1 ≠ i0)
  by_cases hCase1 : extQuad.Nonempty
  · exact upper_case1 hm Q hdeg i0 hCase1
  · have hnoExtQ : ∀ E : Finset (V m), Q i0 E ≠ 0 → E.card = 2 → ∃ v ∈ E, v.1 = i0 := by
      intro E hQ h2
      by_contra h
      push_neg at h
      exact hCase1 ⟨E, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hQ, h2, h⟩⟩
    let mixExt := Finset.univ.filter (fun w : V m =>
      w.1 ≠ i0 ∧ ∃ j : Fin 3, Q i0 {(i0, j), w} ≠ 0)
    by_cases hCase2 : mixExt.Nonempty
    · exact upper_case2 hm Q hdeg hnoloc i0 hnoExtQ hCase2
    · have hdeg1 : ∀ S, Q i0 S ≠ 0 → S.card ≤ 1 := by
        intro S hSnz
        have hle := hdeg i0 S hSnz
        by_contra hgt
        have h2 : S.card = 2 := by omega
        obtain ⟨u, huS, hui0⟩ := hnoExtQ S hSnz h2
        by_cases hsub : S ⊆ block i0
        · have := hnoloc i0 S hSnz hsub; omega
        · obtain ⟨w', hw'S, hw'not⟩ := Finset.not_subset.mp hsub
          have hw'ext : w'.1 ≠ i0 := fun h => hw'not (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
          have huw' : u ≠ w' := fun h => hw'ext (h ▸ hui0)
          have hSeq : S = {(i0, u.2), w'} := by
            have huEq : u = (i0, u.2) := Prod.ext hui0 rfl
            rw [← huEq]
            refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
            · intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx2
              · exact huS
              · rw [Finset.mem_singleton.mp hx2]; exact hw'S
            · rw [Finset.card_pair huw', h2]
          exact hCase2 ⟨w', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw'ext, u.2, hSeq ▸ hSnz⟩⟩
      let extLin := Finset.univ.filter (fun w : V m => w.1 ≠ i0 ∧ Q i0 {w} ≠ 0)
      by_cases hCase3a : extLin.Nonempty
      · exact upper_case3a hm Q hdeg i0 hdeg1 hCase3a
      · exact upper_case3b hm Q hdeg i0 hQne hdeg1 hCase3a

-- Bridge between Bool polynomial representation and ZMod 2 evalPoly
lemma low_to_poly {m : ℕ} (f : W m → Bool)
    (hf : ∃ terms : Finset (Finset (V m)), (∀ mon ∈ terms, mon.card < 3) ∧
      ∀ x, f x = (((terms.filter (fun mon => ∀ a ∈ mon, x a = true)).card % 2) == 1))
    (ebit : Bool) :
    ∃ Q : Finset (V m) → ZMod 2, (∀ S, Q S ≠ 0 → S.card ≤ 2) ∧
      ∀ x, (if xor (f x) ebit then (1 : ZMod 2) else 0) = evalPoly Q x := by
  classical
  obtain ⟨terms, hcard, hfeq⟩ := hf
  let Q0 : Finset (V m) → ZMod 2 := fun S => if S ∈ terms then 1 else 0
  let Q : Finset (V m) → ZMod 2 := Q0 + (fun S => if S = ∅ ∧ ebit = true then 1 else 0)
  refine ⟨Q, ?_, ?_⟩
  · intro S hSnz
    by_cases hS0 : S = ∅
    · rw [hS0]; simp
    · simp only [Q, Q0, Pi.add_apply, hS0, false_and, ↓reduceIte, add_zero] at hSnz
      have hmem : S ∈ terms := by by_contra h; simp [h] at hSnz
      have := hcard S hmem; omega
  · intro x
    have hQ0 : evalPoly Q0 x = (if f x then 1 else 0) := by
      rw [hfeq x]
      unfold evalPoly Q0 chi
      have h1 : (∑ S : Finset (V m), (if S ∈ terms then (1 : ZMod 2) else 0) *
          (if ∀ a ∈ S, x a = true then 1 else 0)) =
          ((terms.filter (fun mon => ∀ a ∈ mon, x a = true)).card : ZMod 2) := by
        rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter]
        rw [← Finset.sum_subset (Finset.subset_univ terms)]
        · refine Finset.sum_congr rfl fun S hS => ?_
          by_cases hp : ∀ a ∈ S, x a = true <;> simp [hS, hp]
        · intro S _ hS; simp [hS]
      rw [h1]
      set k := (terms.filter (fun mon => ∀ a ∈ mon, x a = true)).card
      have hk : (k : ZMod 2) = ((k % 2 : ℕ) : ZMod 2) := by
        have := Nat.div_add_mod k 2
        have h2 : (2 : ZMod 2) = 0 := by decide
        conv_lhs => rw [← this]
        rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, h2, zero_mul, zero_add]
      rw [hk]
      rcases Nat.mod_two_eq_zero_or_one k with h0 | h1
      · rw [h0]; decide
      · rw [h1]; decide
    have hQ1 : evalPoly (fun S => if S = ∅ ∧ ebit = true then (1 : ZMod 2) else 0) x =
        (if ebit then 1 else 0) := by
      unfold evalPoly chi
      rw [Finset.sum_eq_single (∅ : Finset (V m))]
      · cases ebit <;> simp
      · intro S _ hSne; simp [hSne]
      · intro h; exact (h (Finset.mem_univ _)).elim
    rw [evalPoly_add, hQ0, hQ1]
    cases f x <;> cases ebit <;> decide

-- Witness construction: hits P e = 43 * 7^(m-2)
lemma witness_exists {m : ℕ} (hm : 2 ≤ m) (e : Fin m → Bool) :
    let V := Fin m × Fin 3
    let W := V → Bool
    let low := fun (f : W → Bool) =>
      ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card < 3) ∧
        ∀ x, f x = (((terms.filter (fun mon => ∀ a ∈ mon, x a = true)).card % 2) == 1)
    let prodBit := fun (x : W) (i : Fin m) => decide (∀ j : Fin 3, x (i, j) = true)
    let hits := fun (P : Fin m → W → Bool) (e : Fin m → Bool) =>
      ((Finset.univ : Finset W).filter (fun x =>
        ∀ i, xor (prodBit x i) (P i x) = e i)).card
    ∃ P, (∀ i, low (P i)) ∧ hits P e = 43 * 7 ^ (m - 2) ∧ hits P e < 7 ^ m := by
  classical
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by intro h; have := congrArg Fin.val h; simp [i0, i1] at this
  let P : Fin m → W m → Bool := fun i x =>
    if i = i0 then xor (x (i0, 0) && x (i1, 0)) (e i0) else e i
  have hPlow : ∀ i,
      ∃ terms : Finset (Finset (V m)), (∀ mon ∈ terms, mon.card < 3) ∧
        ∀ x, P i x = (((terms.filter (fun mon => ∀ a ∈ mon, x a = true)).card % 2) == 1) := by
    intro i
    by_cases hi : i = i0
    · subst hi
      let M : Finset (V m) := {(i0, 0), (i1, 0)}
      have hMne : M ≠ ∅ := by simp [M]
      have hMcard : M.card = 2 := Finset.card_pair (fun h => h01 (congrArg Prod.fst h))
      cases he : e i0
      · refine ⟨{M}, fun mon hmon => by rw [Finset.mem_singleton.mp hmon, hMcard]; omega, fun x => ?_⟩
        simp only [P, ↓reduceIte, he, Bool.xor_false]
        cases h1 : x (i0, 0) <;> cases h2 : x (i1, 0)
        · have hf : ({M} : Finset (Finset (V m))).filter (fun mon => ∀ a ∈ mon, x a = true) = ∅ := by
            ext mon; simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
            rintro ⟨rfl, hm⟩; exact Bool.false_ne_true (h1 ▸ hm (i0, 0) (by simp [M]))
          rw [hf]; rfl
        · have hf : ({M} : Finset (Finset (V m))).filter (fun mon => ∀ a ∈ mon, x a = true) = ∅ := by
            ext mon; simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
            rintro ⟨rfl, hm⟩; exact Bool.false_ne_true (h1 ▸ hm (i0, 0) (by simp [M]))
          rw [hf]; rfl
        · have hf : ({M} : Finset (Finset (V m))).filter (fun mon => ∀ a ∈ mon, x a = true) = ∅ := by
            ext mon; simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false]
            rintro ⟨rfl, hm⟩; exact Bool.false_ne_true (h2 ▸ hm (i1, 0) (by simp [M]))
          rw [hf]; rfl
        · have hf : ({M} : Finset (Finset (V m))).filter (fun mon => ∀ a ∈ mon, x a = true) = {M} := by
            ext mon
            simp only [Finset.mem_filter, Finset.mem_singleton, and_iff_left_iff_imp]
            rintro rfl a ha
            simp only [M, Finset.mem_insert, Finset.mem_singleton] at ha
            rcases ha with rfl | rfl <;> assumption
          rw [hf, Finset.card_singleton]; rfl
      · refine ⟨{M, ∅}, fun mon hmon => by
          rcases Finset.mem_insert.mp hmon with rfl | h2
          · rw [hMcard]; omega
          · rw [Finset.mem_singleton.mp h2]; simp, fun x => ?_⟩
        simp only [P, ↓reduceIte, he, Bool.xor_true]
        cases h1 : x (i0, 0) <;> cases h2 : x (i1, 0)
        · have hf : ({M, ∅} : Finset (Finset (V m))).filter (fun mon => ∀ a ∈ mon, x a = true) = {∅} := by
            ext mon; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨rfl | rfl, hm⟩
              · exact (Bool.false_ne_true (h1 ▸ hm (i0, 0) (by simp [M]))).elim
              · rfl
            · rintro rfl; exact ⟨Or.inr rfl, by simp⟩
          rw [hf, Finset.card_singleton]; rfl
        · have hf : ({M, ∅} : Finset (Finset (V m))).filter (fun mon => ∀ a ∈ mon, x a = true) = {∅} := by
            ext mon; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨rfl | rfl, hm⟩
              · exact (Bool.false_ne_true (h1 ▸ hm (i0, 0) (by simp [M]))).elim
              · rfl
            · rintro rfl; exact ⟨Or.inr rfl, by simp⟩
          rw [hf, Finset.card_singleton]; rfl
        · have hf : ({M, ∅} : Finset (Finset (V m))).filter (fun mon => ∀ a ∈ mon, x a = true) = {∅} := by
            ext mon; simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
            constructor
            · rintro ⟨rfl | rfl, hm⟩
              · exact (Bool.false_ne_true (h2 ▸ hm (i1, 0) (by simp [M]))).elim
              · rfl
            · rintro rfl; exact ⟨Or.inr rfl, by simp⟩
          rw [hf, Finset.card_singleton]; rfl
        · have hf : ({M, ∅} : Finset (Finset (V m))).filter (fun mon => ∀ a ∈ mon, x a = true) = {M, ∅} := by
            ext mon
            simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, and_iff_left_iff_imp]
            rintro (rfl | rfl) a ha
            · simp only [M, Finset.mem_insert, Finset.mem_singleton] at ha
              rcases ha with rfl | rfl <;> assumption
            · exact (Finset.notMem_empty _ ha).elim
          rw [hf, Finset.card_pair hMne]; rfl
    · cases he : e i
      · refine ⟨∅, by simp, fun x => by simp [P, hi, he]⟩
      · refine ⟨{∅}, fun mon hmon => by rw [Finset.mem_singleton.mp hmon]; simp, fun x => ?_⟩
        simp only [P, if_neg hi, he]
        have hf : ({∅} : Finset (Finset (V m))).filter (fun mon => ∀ a ∈ mon, x a = true) = {∅} := by
          ext mon
          simp only [Finset.mem_filter, Finset.mem_singleton, and_iff_left_iff_imp]
          rintro rfl a ha; exact (Finset.notMem_empty _ ha).elim
        rw [hf, Finset.card_singleton]; rfl
  let B3 := Fin 3 → Bool
  let Good2 := (Finset.univ : Finset (B3 × B3)).filter (fun p =>
    decide (∀ j : Fin 3, p.1 j = true) = (p.1 0 && p.2 0) ∧
    decide (∀ j : Fin 3, p.2 j = true) = false)
  have hGood2 : Good2.card = 43 := by decide
  let Sub3 := {f : B3 // decide (∀ j : Fin 3, f j = true) = false}
  have hSub3 : Fintype.card Sub3 = 7 := by decide
  let Rest := {i : Fin m // i ≠ i0 ∧ i ≠ i1}
  let HitSet := (Finset.univ : Finset (W m)).filter (fun x =>
    ∀ i, xor (decide (∀ j : Fin 3, x (i, j) = true)) (P i x) = e i)
  have hcond : ∀ x : W m, x ∈ HitSet ↔
      (decide (∀ j : Fin 3, x (i0, j) = true) = (x (i0, 0) && x (i1, 0))) ∧
      (∀ i : Fin m, i ≠ i0 → decide (∀ j : Fin 3, x (i, j) = true) = false) := by
    intro x
    simp only [HitSet, Finset.mem_filter, Finset.mem_univ, true_and, P]
    constructor
    · intro h
      refine ⟨?_, fun i hi => ?_⟩
      · have h0 := h i0; simp only [↓reduceIte] at h0
        cases hb : decide (∀ j : Fin 3, x (i0, j) = true) <;>
          cases hc : (x (i0, 0) && x (i1, 0)) <;> cases he : e i0 <;> simp_all
      · have hi' := h i; simp only [if_neg hi] at hi'
        cases hb : decide (∀ j : Fin 3, x (i, j) = true) <;> cases he : e i <;> simp_all
    · rintro ⟨h0, hrest⟩ i
      by_cases hi : i = i0
      · subst hi; simp only [↓reduceIte, h0]
        cases (x (i0, 0) && x (i1, 0)) <;> cases e i0 <;> rfl
      · simp only [if_neg hi, hrest i hi, Bool.false_xor]
  let equiv : ↥HitSet ≃ (↥Good2 × (Rest → Sub3)) :=
    { toFun := fun ⟨x, hx⟩ =>
        let ⟨h0, hrest⟩ := (hcond x).mp hx
        (⟨(fun j => x (i0, j), fun j => x (i1, j)),
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0, hrest i1 h01.symm⟩⟩,
         fun ⟨i, hi0, _⟩ => ⟨fun j => x (i, j), hrest i hi0⟩)
      invFun := fun ⟨⟨⟨f0, f1⟩, hf⟩, g⟩ =>
        ⟨fun v => if h0 : v.1 = i0 then f0 v.2 else if h1 : v.1 = i1 then f1 v.2 else (g ⟨v.1, h0, h1⟩).1 v.2,
         (hcond _).mpr ⟨by
           have hf' := (Finset.mem_filter.mp hf).2.1
           simpa [h01.symm] using hf',
           fun i hi0 => by
             by_cases hi1 : i = i1
             · subst hi1; simpa [hi0] using (Finset.mem_filter.mp hf).2.2
             · simpa [hi0, hi1] using (g ⟨i, hi0, hi1⟩).2⟩⟩
      left_inv := fun ⟨x, _⟩ => by
        ext ⟨a, b⟩
        by_cases h0 : a = i0
        · subst h0; simp
        · by_cases h1 : a = i1
          · subst h1; simp [h0]
          · simp [h0, h1]
      right_inv := fun ⟨⟨⟨f0, f1⟩, hf⟩, g⟩ => by
        apply Prod.ext
        · apply Subtype.ext; apply Prod.ext
          · funext j; simp
          · funext j; simp [h01.symm]
        · funext ⟨i, hi0, hi1⟩; apply Subtype.ext; funext j; simp [hi0, hi1] }
  have hcardRest : Fintype.card Rest = m - 2 := by
    have hset : (Finset.univ.filter (fun i : Fin m => i ≠ i0 ∧ i ≠ i1)) = (Finset.univ.erase i0).erase i1 := by
      ext i; simp [and_comm]
    have h1 : Fintype.card Rest = (Finset.univ.filter (fun i : Fin m => i ≠ i0 ∧ i ≠ i1)).card :=
      Fintype.card_subtype _
    rw [h1, hset, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨h01.symm, Finset.mem_univ _⟩),
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_fin]
    omega
  have hcard : HitSet.card = 43 * 7 ^ (m - 2) := by
    calc HitSet.card = Fintype.card ↥HitSet := (Fintype.card_coe _).symm
      _ = Fintype.card (↥Good2 × (Rest → Sub3)) := Fintype.card_congr equiv
      _ = 43 * 7 ^ (m - 2) := by
          rw [Fintype.card_prod, Fintype.card_coe, hGood2, Fintype.card_fun, hSub3, hcardRest]
  refine ⟨P, hPlow, hcard, ?_⟩
  change HitSet.card < 7 ^ m
  rw [hcard]
  have h7m : 7 ^ m = 49 * 7 ^ (m - 2) := by
    have : m = (m - 2) + 2 := by omega
    conv_lhs => rw [this, pow_add]
    ring
  have hpos : 0 < 7 ^ (m - 2) := by positivity
  omega

lemma card_all_block_zero (m : ℕ) :
    ((Finset.univ : Finset (W m)).filter (fun x => ∀ i : Fin m, chi (block i) x = 0)).card = 7 ^ m := by
  classical
  let Sub3 := {f : Fin 3 → Bool // ¬ ∀ j : Fin 3, f j = true}
  have hSub3 : Fintype.card Sub3 = 7 := by decide
  let S0 := (Finset.univ : Finset (W m)).filter (fun x => ∀ i : Fin m, chi (block i) x = 0)
  have hchi0 : ∀ (x : W m) (i : Fin m), chi (block i) x = 0 ↔ ¬ ∀ j : Fin 3, x (i, j) = true := by
    intro x i
    unfold chi
    have heq : (∀ a ∈ block i, x a = true) ↔ (∀ j : Fin 3, x (i, j) = true) := by
      constructor
      · intro h j; exact h (i, j) (by simp [block])
      · intro h ⟨a, b⟩ hab
        have ha : a = i := (Finset.mem_filter.mp hab).2
        subst ha; exact h b
    by_cases h : ∀ j : Fin 3, x (i, j) = true
    · rw [if_pos (heq.mpr h)]; simp [h]
    · rw [if_neg (mt heq.mp h)]; simp [h]
  let equiv : ↥S0 ≃ (Fin m → Sub3) :=
    { toFun := fun ⟨x, hx⟩ i =>
        ⟨fun j => x (i, j), (hchi0 x i).mp ((Finset.mem_filter.mp hx).2 i)⟩
      invFun := fun g =>
        ⟨fun v => (g v.1).1 v.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i =>
          (hchi0 _ i).mpr (g i).2⟩⟩
      left_inv := fun ⟨x, _⟩ => by ext ⟨a, b⟩; rfl
      right_inv := fun g => by funext i; apply Subtype.ext; funext j; rfl }
  calc S0.card = Fintype.card ↥S0 := (Fintype.card_coe _).symm
    _ = Fintype.card (Fin m → Sub3) := Fintype.card_congr equiv
    _ = 7 ^ m := by rw [Fintype.card_fun, Fintype.card_fin, hSub3]

lemma upper_general {m : ℕ} (hm : 2 ≤ m) (e : Fin m → Bool) (P : Fin m → W m → Bool)
    (hP : ∀ i, ∃ terms : Finset (Finset (V m)), (∀ mon ∈ terms, mon.card < 3) ∧
      ∀ x, P i x = (((terms.filter (fun mon => ∀ a ∈ mon, x a = true)).card % 2) == 1))
    (hlt : ((Finset.univ : Finset (W m)).filter (fun x =>
      ∀ i, xor (decide (∀ j : Fin 3, x (i, j) = true)) (P i x) = e i)).card < 7 ^ m) :
    ((Finset.univ : Finset (W m)).filter (fun x =>
      ∀ i, xor (decide (∀ j : Fin 3, x (i, j) = true)) (P i x) = e i)).card ≤ 43 * 7 ^ (m - 2) := by
  classical
  have hQex : ∀ i, ∃ Q : Finset (V m) → ZMod 2, (∀ S, Q S ≠ 0 → S.card ≤ 2) ∧
      ∀ x, (if xor (P i x) (e i) then (1 : ZMod 2) else 0) = evalPoly Q x :=
    fun i => low_to_poly (P i) (hP i) (e i)
  choose Q hQdeg hQeval using hQex
  -- Global coordinate flip killing all local quadratic terms simultaneously
  let c : V m → Bool := fun v => decide (Q v.1 ((block v.1).erase v) ≠ 0)
  have hflipEx : ∀ i, ∃ Qf : Finset (V m) → ZMod 2, (∀ S, Qf S ≠ 0 → S.card ≤ 2) ∧
      (∀ T, T.card = 2 → Qf T = Q i T) ∧ ∀ x, evalPoly (Q i) (flipW c x) = evalPoly Qf x :=
    fun i => flip_low c (Q i) (hQdeg i)
  choose Qf hQfdeg hQf2 hQfeval using hflipEx
  let Q' : Fin m → Finset (V m) → ZMod 2 := fun i => blockFlipRem c i + Qf i
  have hQ'deg : ∀ i S, Q' i S ≠ 0 → S.card ≤ 2 := by
    intro i S hSnz
    by_cases h1 : blockFlipRem c i S = 0
    · simp only [Q', Pi.add_apply, h1, zero_add] at hSnz
      exact hQfdeg i S hSnz
    · exact blockFlipRem_deg c i S h1
  have hQ'noloc : ∀ i S, Q' i S ≠ 0 → S ⊆ block i → S.card ≤ 1 := by
    intro i S hSnz hsub
    have h2 := hQ'deg i S hSnz
    by_contra hgt
    have hSc2 : S.card = 2 := by omega
    have hdiffCard : (block i \ S).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, card_block, hSc2]
    obtain ⟨v, hvEq⟩ := Finset.card_eq_one.mp hdiffCard
    have hvMem : v ∈ block i \ S := by rw [hvEq]; exact Finset.mem_singleton_self v
    have hvi : v.1 = i := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hvMem).1).2
    have hSeq : S = (block i).erase (i, v.2) := by
      have hvDef : v = (i, v.2) := Prod.ext hvi rfl
      ext u
      simp only [Finset.mem_erase]
      constructor
      · intro hu
        refine ⟨fun huv => (Finset.mem_sdiff.mp hvMem).2 (hvDef ▸ huv ▸ hu), hsub hu⟩
      · rintro ⟨hne, hub⟩
        by_contra huS
        have : u ∈ block i \ S := Finset.mem_sdiff.mpr ⟨hub, huS⟩
        rw [hvEq, Finset.mem_singleton] at this
        exact hne (this.trans hvDef)
    have hzero : Q' i S = 0 := by
      rw [hSeq]
      simp only [Q', Pi.add_apply, blockFlipRem_erase]
      have hcardE : ((block i).erase (i, v.2)).card = 2 := by
        rw [Finset.card_erase_of_mem (by simp [block]), card_block]
      rw [hQf2 i _ hcardE]
      dsimp only [c]
      have hcancel : ∀ a : ZMod 2, (if decide (a ≠ 0) = true then (1 : ZMod 2) else 0) + a = 0 := by
        intro a; fin_cases a <;> decide
      exact hcancel _
    exact hSnz hzero
  -- Relate HitSet to H' via bijection flipW c
  let HitSet := (Finset.univ : Finset (W m)).filter (fun x =>
    ∀ i, xor (decide (∀ j : Fin 3, x (i, j) = true)) (P i x) = e i)
  let H' := (Finset.univ : Finset (W m)).filter (fun x =>
    ∀ i, chi (block i) x + evalPoly (Q' i) x = 0)
  have hiff : ∀ x : W m, flipW c x ∈ HitSet ↔ x ∈ H' := by
    intro x
    simp only [HitSet, H', Finset.mem_filter, Finset.mem_univ, true_and]
    refine forall_congr' fun i => ?_
    have hchi : chi (block i) (flipW c x) = if decide (∀ j : Fin 3, flipW c x (i, j) = true) then 1 else 0 := by
      unfold chi
      have heq : (∀ a ∈ block i, flipW c x a = true) ↔ (∀ j : Fin 3, flipW c x (i, j) = true) := by
        constructor
        · intro h j; exact h (i, j) (by simp [block])
        · intro h ⟨a, b⟩ hab
          have ha : a = i := (Finset.mem_filter.mp hab).2
          subst ha; exact h b
      by_cases h : ∀ j : Fin 3, flipW c x (i, j) = true
      · rw [if_pos (heq.mpr h)]; simp [h]
      · rw [if_neg (mt heq.mp h)]; simp [h]
    have hev : chi (block i) x + evalPoly (Q' i) x =
        chi (block i) (flipW c x) + evalPoly (Q i) (flipW c x) := by
      rw [evalPoly_blockFlipRem c i x, hQfeval i x]
      simp only [Q', evalPoly_add]
      ring
    rw [hev, hchi, ← hQeval i (flipW c x)]
    cases decide (∀ j : Fin 3, flipW c x (i, j) = true) <;>
      cases P i (flipW c x) <;> cases e i <;> decide
  have hcardEq : HitSet.card = H'.card := by
    refine Finset.card_bij (fun x _ => flipW c x) ?_ ?_ ?_
    · intro x hx; exact (hiff (flipW c x)).mp (by rw [flipW_invol]; exact hx)
    · intro x1 _ x2 _ h
      have := congrArg (flipW c) h
      rwa [flipW_invol, flipW_invol] at this
    · intro y hy
      exact ⟨flipW c y, (hiff y).mpr hy, flipW_invol c y⟩
  by_cases hall0 : ∀ i : Fin m, Q' i = 0
  · exfalso
    have hH'eq : H' = (Finset.univ : Finset (W m)).filter (fun x => ∀ i : Fin m, chi (block i) x = 0) := by
      ext x
      simp only [H', Finset.mem_filter, Finset.mem_univ, true_and]
      refine forall_congr' fun i => ?_
      rw [hall0 i, evalPoly_zero, add_zero]
    have h7 : H'.card = 7 ^ m := by rw [hH'eq]; exact card_all_block_zero m
    rw [hcardEq, h7] at hlt
    exact lt_irrefl _ hlt
  · push_neg at hall0
    obtain ⟨i0, hi0ne⟩ := hall0
    rw [hcardEq]
    exact upper_normalized hm Q' hQ'deg hQ'noloc i0 hi0ne

end PEqualNP.Outside.L_lib_590_aux

theorem PEqualNP.Outside.L_lib_590 :
    ∀ (m : ℕ), 2 ≤ m →
      let r := 3
      let V := Fin m × Fin r
      let W := V → Bool
      let low := fun (f : W → Bool) =>
        ∃ terms : Finset (Finset V), (∀ mon ∈ terms, mon.card < r) ∧
          ∀ x, f x = (((terms.filter (fun mon => ∀ a ∈ mon, x a = true)).card % 2) == 1)
      let prodBit := fun (x : W) (i : Fin m) => decide (∀ j : Fin r, x (i,j) = true)
      let hits := fun (P : Fin m → W → Bool) (e : Fin m → Bool) =>
        ((Finset.univ : Finset W).filter (fun x =>
          ∀ i, xor (prodBit x i) (P i x) = e i)).card
      ∀ e : Fin m → Bool,
        (∀ P, (∀ i, low (P i)) → hits P e < 7^m → hits P e ≤ 43 * 7^(m-2)) ∧
        (∃ P, (∀ i, low (P i)) ∧ hits P e = 43 * 7^(m-2) ∧ hits P e < 7^m) := by
  intro m hm r V W low prodBit hits e
  exact ⟨fun P hP hlt => PEqualNP.Outside.L_lib_590_aux.upper_general hm e P hP hlt,
         PEqualNP.Outside.L_lib_590_aux.witness_exists hm e⟩
