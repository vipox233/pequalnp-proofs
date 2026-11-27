import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Outside.L_lib_629_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

private abbrev F := ZMod 2
private abbrev Vec (n : ℕ) := Fin n → F
private abbrev Mat (n : ℕ) := Fin n → Fin n → F

private def b2z (b : Bool) : F := if b then 1 else 0

private theorem z2_cases (x : F) : x = 0 ∨ x = 1 := by
  fin_cases x
  · left; rfl
  · right; rfl

private theorem z2_add_self (x : F) : x + x = 0 := by
  rcases z2_cases x with rfl | rfl <;> decide

private theorem z2_sub_eq_add (x y : F) : x - y = x + y := by
  rcases z2_cases x with rfl | rfl <;> rcases z2_cases y with rfl | rfl <;> decide

private theorem z2_eq_iff_add_eq_zero (x y : F) : x = y ↔ x + y = 0 := by
  rcases z2_cases x with rfl | rfl <;> rcases z2_cases y with rfl | rfl <;> decide

private theorem b2z_decide_ne_zero (x : F) : b2z (decide (x ≠ 0)) = x := by
  rcases z2_cases x with rfl | rfl <;> decide

private theorem b2z_not (b : Bool) : b2z (!b) = 1 + b2z b := by
  cases b <;> decide

private theorem b2z_and (a b : Bool) : b2z (a && b) = b2z a * b2z b := by
  cases a <;> cases b <;> decide

private theorem b2z_xor_gate (a b : Bool) :
    b2z ((a || b) && !(a && b)) = b2z a + b2z b := by
  cases a <;> cases b <;> decide

private def lowSet (n d : ℕ) : Finset (Finset (Fin n)) :=
  Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ d)

private theorem empty_mem_lowSet (n d : ℕ) : (∅ : Finset (Fin n)) ∈ lowSet n d := by
  simp [lowSet]

private theorem lowSet_card_pos (n d : ℕ) : 0 < (lowSet n d).card :=
  Finset.card_pos.mpr ⟨∅, empty_mem_lowSet n d⟩

private theorem mem_lowSet_of_subset {n d : ℕ} {S T : Finset (Fin n)}
    (hS : S ∈ lowSet n d) (hTS : T ⊆ S) : T ∈ lowSet n d := by
  simp only [lowSet, Finset.mem_filter, Finset.mem_univ, true_and] at hS ⊢
  exact le_trans (Finset.card_le_card hTS) hS

private def ind {n : ℕ} (S : Finset (Fin n)) : Vec n :=
  fun i => if i ∈ S then 1 else 0

private def monom {n : ℕ} (S : Finset (Fin n)) (x : Vec n) : F :=
  ∏ i ∈ S, x i

private def evalPoly {n : ℕ} (d : ℕ) (c : Finset (Fin n) → F) (x : Vec n) : F :=
  ∑ S ∈ lowSet n d, c S * monom S x

private theorem monom_ind {n : ℕ} (U T : Finset (Fin n)) :
    monom U (ind T) = if U ⊆ T then 1 else 0 := by
  unfold monom ind
  by_cases h : U ⊆ T
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    rw [if_pos (h hi)]
  · rw [if_neg h]
    rw [Finset.not_subset] at h
    obtain ⟨i, hiU, hiT⟩ := h
    apply Finset.prod_eq_zero hiU
    rw [if_neg hiT]

private def mobiusStep {n : ℕ} (i : Fin n) (a : Finset (Fin n) → F) (S : Finset (Fin n)) : F :=
  if i ∈ S then a S + a (S.erase i) else a S

private def mobiusFold {n : ℕ} (l : List (Fin n)) (g : Finset (Fin n) → F) : Finset (Fin n) → F :=
  l.foldl (fun a i => mobiusStep i a) g

private def mobius {n : ℕ} (g : Finset (Fin n) → F) : Finset (Fin n) → F :=
  mobiusFold (List.finRange n) g

private theorem mobiusFold_spec {n : ℕ} (l : List (Fin n)) (hl : l.Nodup)
    (g : Finset (Fin n) → F) (S : Finset (Fin n)) :
    mobiusFold l g S = ∑ T ∈ S.powerset.filter (fun T => ∀ r, r ∈ S \ T → r ∈ l), g T := by
  induction l generalizing g with
  | nil =>
    simp only [mobiusFold, List.foldl_nil]
    have hfilt : S.powerset.filter (fun T => ∀ r, r ∈ S \ T → r ∈ ([] : List (Fin n))) = {S} := by
      ext T
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton, List.not_mem_nil,
        imp_false, Finset.mem_sdiff, not_and, not_not]
      constructor
      · intro ⟨hTS, hST⟩
        exact Finset.Subset.antisymm hTS (fun r hr => hST r hr)
      · intro h; subst h; exact ⟨Finset.Subset.rfl, fun _ h => h⟩
    rw [hfilt, Finset.sum_singleton]
  | cons i ls ih =>
    have hni : i ∉ ls := (List.nodup_cons.mp hl).1
    have hls : ls.Nodup := (List.nodup_cons.mp hl).2
    simp only [mobiusFold, List.foldl_cons]
    change mobiusFold ls (mobiusStep i g) S = _
    rw [ih hls (mobiusStep i g)]
    by_cases hiS : i ∈ S
    · have hA : ∀ T ∈ S.powerset.filter (fun T => ∀ r, r ∈ S \ T → r ∈ ls), i ∈ T := by
        intro T hT
        simp only [Finset.mem_filter, Finset.mem_powerset] at hT
        by_contra hiT
        exact hni (hT.2 i (Finset.mem_sdiff.mpr ⟨hiS, hiT⟩))
      have hsum1 : ∑ T ∈ S.powerset.filter (fun T => ∀ r, r ∈ S \ T → r ∈ ls), mobiusStep i g T =
          (∑ T ∈ S.powerset.filter (fun T => ∀ r, r ∈ S \ T → r ∈ ls), g T) +
          (∑ T ∈ S.powerset.filter (fun T => ∀ r, r ∈ S \ T → r ∈ ls), g (T.erase i)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun T hT => ?_
        simp only [mobiusStep, if_pos (hA T hT)]
      rw [hsum1]
      let A := S.powerset.filter (fun T => ∀ r, r ∈ S \ T → r ∈ ls)
      let B := S.powerset.filter (fun T => (∀ r, r ∈ S \ T → r ∈ i :: ls) ∧ i ∉ T)
      have hsum2 : ∑ T ∈ A, g (T.erase i) = ∑ T ∈ B, g T := by
        refine Finset.sum_bij (fun T _ => T.erase i) ?_ ?_ ?_ ?_
        · intro T hT
          simp only [A, B, Finset.mem_filter, Finset.mem_powerset, List.mem_cons] at hT ⊢
          refine ⟨Finset.Subset.trans (Finset.erase_subset i T) hT.1, ⟨?_, Finset.notMem_erase i T⟩⟩
          intro r hr
          rw [Finset.mem_sdiff, Finset.mem_erase, not_and] at hr
          by_cases hri : r = i
          · exact Or.inl hri
          · exact Or.inr (hT.2 r (Finset.mem_sdiff.mpr ⟨hr.1, fun h => hr.2 hri h⟩))
        · intro T1 hT1 T2 hT2 heq
          have hi1 : i ∈ T1 := hA T1 hT1
          have hi2 : i ∈ T2 := hA T2 hT2
          rw [← Finset.insert_erase hi1, ← Finset.insert_erase hi2, heq]
        · intro T hT
          simp only [B, Finset.mem_filter, Finset.mem_powerset, List.mem_cons] at hT
          refine ⟨insert i T, ?_, Finset.erase_insert hT.2.2⟩
          simp only [A, Finset.mem_filter, Finset.mem_powerset]
          refine ⟨Finset.insert_subset hiS hT.1, ?_⟩
          intro r hr
          rw [Finset.mem_sdiff, Finset.mem_insert, not_or] at hr
          rcases hT.2.1 r (Finset.mem_sdiff.mpr ⟨hr.1, hr.2.2⟩) with rfl | hls'
          · exact False.elim (hr.2.1 rfl)
          · exact hls'
        · intro _ _; rfl
      rw [hsum2, ← Finset.sum_union]
      · congr 1
        ext T
        simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_powerset, List.mem_cons]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2, _⟩)
          · exact ⟨h1, fun r hr => Or.inr (h2 r hr)⟩
          · exact ⟨h1, h2⟩
        · intro ⟨h1, h2⟩
          by_cases hiT : i ∈ T
          · left
            refine ⟨h1, fun r hr => ?_⟩
            rcases h2 r hr with rfl | hls'
            · exact False.elim ((Finset.mem_sdiff.mp hr).2 hiT)
            · exact hls'
          · right
            exact ⟨h1, h2, hiT⟩
      · rw [Finset.disjoint_left]
        intro T hTA hTB
        have hiT : i ∈ T := hA T hTA
        simp only [B, Finset.mem_filter] at hTB
        exact hTB.2.2 hiT
    · have hfilt : S.powerset.filter (fun T => ∀ r, r ∈ S \ T → r ∈ ls) =
          S.powerset.filter (fun T => ∀ r, r ∈ S \ T → r ∈ i :: ls) := by
        ext T
        simp only [Finset.mem_filter, Finset.mem_powerset, List.mem_cons]
        constructor
        · intro ⟨h1, h2⟩; exact ⟨h1, fun r hr => Or.inr (h2 r hr)⟩
        · intro ⟨h1, h2⟩
          refine ⟨h1, fun r hr => ?_⟩
          rcases h2 r hr with rfl | hls'
          · exact False.elim (hiS (Finset.mem_sdiff.mp hr).1)
          · exact hls'
      rw [← hfilt]
      refine Finset.sum_congr rfl fun T hT => ?_
      simp only [Finset.mem_filter, Finset.mem_powerset] at hT
      have hiT : i ∉ T := fun h => hiS (hT.1 h)
      simp only [mobiusStep, if_neg hiT]

private theorem mobius_eq_sum {n : ℕ} (g : Finset (Fin n) → F) (S : Finset (Fin n)) :
    mobius g S = ∑ T ∈ S.powerset, g T := by
  unfold mobius
  rw [mobiusFold_spec (List.finRange n) (List.nodup_finRange n) g S]
  congr 1
  ext T
  simp [List.mem_finRange]

private theorem mobius_recover {n d : ℕ} {f : Vec n → F} {c : Finset (Fin n) → F}
    (hf : ∀ x, f x = evalPoly d c x) {S : Finset (Fin n)} (hS : S ∈ lowSet n d) :
    mobius (fun T => f (ind T)) S = c S := by
  rw [mobius_eq_sum]
  have hterm : ∀ T ∈ S.powerset, f (ind T) = ∑ U ∈ T.powerset, c U := by
    intro T hT
    rw [Finset.mem_powerset] at hT
    rw [hf (ind T)]
    unfold evalPoly
    have hsub : T.powerset ⊆ lowSet n d := by
      intro U hU
      rw [Finset.mem_powerset] at hU
      exact mem_lowSet_of_subset hS (Finset.Subset.trans hU hT)
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun U hU => ?_
      rw [Finset.mem_powerset] at hU
      rw [monom_ind, if_pos hU, mul_one]
    · intro U _ hUn
      rw [Finset.mem_powerset] at hUn
      rw [monom_ind, if_neg hUn, mul_zero]
  rw [Finset.sum_congr rfl hterm]
  have hswap : (∑ T ∈ S.powerset, ∑ U ∈ T.powerset, c U) =
      ∑ U ∈ S.powerset, ∑ T ∈ S.powerset.filter (fun T => U ⊆ T), c U := by
    have h1 : ∀ T ∈ S.powerset, (∑ U ∈ T.powerset, c U) =
        ∑ U ∈ S.powerset, if U ⊆ T then c U else 0 := by
      intro T hT
      rw [Finset.mem_powerset] at hT
      rw [← Finset.sum_filter]
      congr 1
      ext U
      simp only [Finset.mem_powerset, Finset.mem_filter]
      exact ⟨fun h => ⟨Finset.Subset.trans h hT, h⟩, fun h => h.2⟩
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun U _ => ?_
    rw [Finset.sum_filter]
  rw [hswap]
  have hinner : ∀ U ∈ S.powerset,
      (∑ _T ∈ S.powerset.filter (fun T => U ⊆ T), c U) = if U = S then c S else 0 := by
    intro U hU
    rw [Finset.mem_powerset] at hU
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : (S.powerset.filter (fun T => U ⊆ T)).card = (S \ U).powerset.card := by
      refine Finset.card_bij (fun T _ => T \ U) ?_ ?_ ?_
      · intro T hT
        simp only [Finset.mem_filter, Finset.mem_powerset] at hT ⊢
        exact Finset.sdiff_subset_sdiff hT.1 Finset.Subset.rfl
      · intro T1 hT1 T2 hT2 heq
        simp only [Finset.mem_filter, Finset.mem_powerset] at hT1 hT2
        rw [← Finset.union_sdiff_of_subset hT1.2, ← Finset.union_sdiff_of_subset hT2.2, heq]
      · intro V hV
        rw [Finset.mem_powerset] at hV
        refine ⟨U ∪ V, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_powerset]
          exact ⟨Finset.union_subset hU (Finset.Subset.trans hV Finset.sdiff_subset), Finset.subset_union_left⟩
        · ext x
          simp only [Finset.mem_sdiff, Finset.mem_union]
          constructor
          · rintro ⟨hxU | hxV, hnxU⟩
            · exact False.elim (hnxU hxU)
            · exact hxV
          · intro hxV
            exact ⟨Or.inr hxV, (Finset.mem_sdiff.mp (hV hxV)).2⟩
    rw [hcard, Finset.card_powerset]
    by_cases hUS : U = S
    · subst hUS
      simp
    · rw [if_neg hUS]
      have hne : (S \ U).Nonempty := by
        by_contra hemp
        rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hemp
        exact hUS (Finset.Subset.antisymm hU hemp)
      have hpos : 0 < (S \ U).card := Finset.card_pos.mpr hne
      have h2 : ((2 ^ (S \ U).card : ℕ) : F) = 0 := by
        obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
        rw [hm, pow_succ, Nat.cast_mul, Nat.cast_ofNat]
        have hzero : (2 : F) = 0 := by decide
        rw [hzero, mul_zero]
      rw [h2, zero_mul]
  rw [Finset.sum_congr rfl hinner]
  simp

private theorem evalPoly_eq_iff {n d : ℕ} {c1 c2 : Finset (Fin n) → F} :
    (∀ x, evalPoly d c1 x = evalPoly d c2 x) ↔ (∀ S ∈ lowSet n d, c1 S = c2 S) := by
  constructor
  · intro h S hS
    have h1 := mobius_recover (f := evalPoly d c1) (c := c1) (fun _ => rfl) hS
    have h2 := mobius_recover (f := evalPoly d c1) (c := c2) h hS
    rw [← h1, h2]
  · intro h x
    unfold evalPoly
    exact Finset.sum_congr rfl fun S hS => by rw [h S hS]

private def shiftCoord {n : ℕ} (d : ℕ) (r : Fin n) (b : F) (c : Finset (Fin n) → F)
    (S : Finset (Fin n)) : F :=
  c S + if r ∉ S ∧ insert r S ∈ lowSet n d then b * c (insert r S) else 0

private def shiftFold {n : ℕ} (d : ℕ) (l : List (Fin n)) (v : Vec n) (c : Finset (Fin n) → F) :
    Finset (Fin n) → F :=
  l.foldl (fun a r => shiftCoord d r (v r) a) c

private def shiftVec {n : ℕ} (d : ℕ) (v : Vec n) (c : Finset (Fin n) → F) : Finset (Fin n) → F :=
  shiftFold d (List.finRange n) v c

private theorem evalPoly_shiftCoord {n : ℕ} (d : ℕ) (r : Fin n) (b : F)
    (c : Finset (Fin n) → F) (x : Vec n) :
    evalPoly d (shiftCoord d r b c) x = evalPoly d c (fun i => x i + if i = r then b else 0) := by
  rcases z2_cases b with rfl | rfl
  · have hsc : ∀ S, shiftCoord d r 0 c S = c S := fun S => by simp [shiftCoord]
    unfold evalPoly
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [hsc S]
    congr 1
    unfold monom
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [ite_self, add_zero]
  · unfold evalPoly shiftCoord
    have hleft : (∑ S ∈ lowSet n d,
        (c S + if r ∉ S ∧ insert r S ∈ lowSet n d then (1 : F) * c (insert r S) else 0) * monom S x) =
        (∑ S ∈ lowSet n d, c S * monom S x) +
        (∑ S ∈ (lowSet n d).filter (fun S => r ∉ S ∧ insert r S ∈ lowSet n d),
          c (insert r S) * monom S x) := by
      simp only [one_mul, add_mul, Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun S _ => ?_
      split_ifs <;> simp
    rw [hleft]
    have hmonom_r : ∀ S : Finset (Fin n),
        monom S (fun i => x i + if i = r then (1 : F) else 0) =
          monom S x + if r ∈ S then monom (S.erase r) x else 0 := by
      intro S
      unfold monom
      by_cases hr : r ∈ S
      · rw [if_pos hr, ← Finset.mul_prod_erase S _ hr, if_pos rfl]
        have hrest : (∏ i ∈ S.erase r, (x i + if i = r then (1 : F) else 0)) =
            ∏ i ∈ S.erase r, x i := by
          refine Finset.prod_congr rfl fun i hi => ?_
          rw [if_neg (Finset.ne_of_mem_erase hi), add_zero]
        rw [hrest, add_mul, one_mul, Finset.mul_prod_erase S x hr]
      · rw [if_neg hr, add_zero]
        refine Finset.prod_congr rfl fun i hi => ?_
        have hne : i ≠ r := fun h => hr (h ▸ hi)
        dsimp only
        rw [if_neg hne, add_zero]
    have hright : (∑ S ∈ lowSet n d, c S * monom S (fun i => x i + if i = r then (1 : F) else 0)) =
        (∑ S ∈ lowSet n d, c S * monom S x) +
        (∑ S ∈ (lowSet n d).filter (fun S => r ∈ S), c S * monom (S.erase r) x) := by
      have h1 : ∀ S ∈ lowSet n d,
          c S * monom S (fun i => x i + if i = r then (1 : F) else 0) =
            c S * monom S x + if r ∈ S then c S * monom (S.erase r) x else 0 := by
        intro S _
        rw [hmonom_r S, mul_add]
        congr 1
        split_ifs <;> simp
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, Finset.sum_filter]
    rw [hright]
    congr 1
    refine Finset.sum_bij (fun S _ => insert r S) ?_ ?_ ?_ ?_
    · intro S hS
      simp only [Finset.mem_filter] at hS ⊢
      exact ⟨hS.2.2, Finset.mem_insert_self r S⟩
    · intro S1 hS1 S2 hS2 heq
      simp only [Finset.mem_filter] at hS1 hS2
      have := congrArg (fun T => T.erase r) heq
      simpa [Finset.erase_insert hS1.2.1, Finset.erase_insert hS2.2.1] using this
    · intro T hT
      simp only [Finset.mem_filter] at hT
      refine ⟨T.erase r, ?_, Finset.insert_erase hT.2⟩
      simp only [Finset.mem_filter]
      exact ⟨mem_lowSet_of_subset hT.1 (Finset.erase_subset r T),
        Finset.notMem_erase r T, by rw [Finset.insert_erase hT.2]; exact hT.1⟩
    · intro S hS
      simp only [Finset.mem_filter] at hS
      rw [Finset.erase_insert hS.2.1]

private theorem evalPoly_shiftFold {n : ℕ} (d : ℕ) (l : List (Fin n)) (hl : l.Nodup)
    (v : Vec n) (c : Finset (Fin n) → F) (x : Vec n) :
    evalPoly d (shiftFold d l v c) x =
      evalPoly d c (fun i => x i + if i ∈ l then v i else 0) := by
  induction l generalizing c x with
  | nil =>
    simp [shiftFold]
  | cons r ls ih =>
    have hnr : r ∉ ls := (List.nodup_cons.mp hl).1
    have hls : ls.Nodup := (List.nodup_cons.mp hl).2
    simp only [shiftFold, List.foldl_cons]
    change evalPoly d (shiftFold d ls v (shiftCoord d r (v r) c)) x = _
    rw [ih hls (shiftCoord d r (v r) c) x, evalPoly_shiftCoord]
    congr 1
    funext i
    simp only [List.mem_cons]
    by_cases hir : i = r
    · subst hir
      simp [hnr]
    · simp [hir]

private theorem evalPoly_shiftVec {n : ℕ} (d : ℕ) (v : Vec n) (c : Finset (Fin n) → F) (x : Vec n) :
    evalPoly d (shiftVec d v c) x = evalPoly d c (x + v) := by
  unfold shiftVec
  rw [evalPoly_shiftFold d (List.finRange n) (List.nodup_finRange n) v c x]
  congr 1
  funext i
  simp [List.mem_finRange]

private theorem shiftCoord_preserves_top {n : ℕ} (d k : ℕ) (r : Fin n) (b : F)
    {a : Finset (Fin n) → F} (ha : ∀ S ∈ lowSet n d, k < S.card → a S = 0) :
    (∀ S ∈ lowSet n d, k < S.card → shiftCoord d r b a S = 0) ∧
    (∀ S ∈ lowSet n d, S.card = k → shiftCoord d r b a S = a S) := by
  constructor
  · intro S hS hk
    unfold shiftCoord
    rw [ha S hS hk, zero_add]
    split_ifs with h
    · have hcard : k < (insert r S).card := by rw [Finset.card_insert_of_notMem h.1]; omega
      rw [ha (insert r S) h.2 hcard, mul_zero]
    · rfl
  · intro S hS hk
    unfold shiftCoord
    split_ifs with h
    · have hcard : k < (insert r S).card := by rw [Finset.card_insert_of_notMem h.1]; omega
      rw [ha (insert r S) h.2 hcard, mul_zero, add_zero]
    · simp

private theorem shiftFold_preserves_top {n : ℕ} (d k : ℕ) (l : List (Fin n)) (v : Vec n)
    {a : Finset (Fin n) → F} (ha : ∀ S ∈ lowSet n d, k < S.card → a S = 0) :
    (∀ S ∈ lowSet n d, k < S.card → shiftFold d l v a S = 0) ∧
    (∀ S ∈ lowSet n d, S.card = k → shiftFold d l v a S = a S) := by
  induction l generalizing a with
  | nil => exact ⟨ha, fun _ _ _ => rfl⟩
  | cons r ls ih =>
    have hstep := shiftCoord_preserves_top d k r (v r) ha
    have hrest := ih hstep.1
    refine ⟨fun S hS hk => ?_, fun S hS hk => ?_⟩
    · change shiftFold d ls v (shiftCoord d r (v r) a) S = 0
      exact hrest.1 S hS hk
    · change shiftFold d ls v (shiftCoord d r (v r) a) S = a S
      rw [hrest.2 S hS hk, hstep.2 S hS hk]

private theorem shiftVec_preserves_top {n : ℕ} (d k : ℕ) (v : Vec n)
    {a : Finset (Fin n) → F} (ha : ∀ S ∈ lowSet n d, k < S.card → a S = 0) :
    (∀ S ∈ lowSet n d, k < S.card → shiftVec d v a S = 0) ∧
    (∀ S ∈ lowSet n d, S.card = k → shiftVec d v a S = a S) :=
  shiftFold_preserves_top d k (List.finRange n) v ha

private def delta {n t : ℕ} (d : ℕ) (c : Fin t → Finset (Fin n) → F) (v : Vec n)
    (j : Fin t) (S : Finset (Fin n)) : F :=
  shiftVec d v (c j) S + c j S

private theorem evalPoly_delta {n t : ℕ} (d : ℕ) (c : Fin t → Finset (Fin n) → F)
    (v : Vec n) (j : Fin t) (x : Vec n) :
    evalPoly d (delta d c v j) x = evalPoly d (c j) (x + v) + evalPoly d (c j) x := by
  rw [← evalPoly_shiftVec]
  unfold evalPoly delta
  simp only [add_mul, Finset.sum_add_distrib]

private theorem delta_zero {n t : ℕ} (d : ℕ) (c : Fin t → Finset (Fin n) → F)
    (j : Fin t) {S : Finset (Fin n)} (hS : S ∈ lowSet n d) :
    delta d c 0 j S = 0 := by
  have hev : ∀ x, evalPoly d (delta d c 0 j) x = evalPoly d (fun _ => 0) x := by
    intro x
    rw [evalPoly_delta, add_zero, z2_add_self]
    simp [evalPoly]
  exact (evalPoly_eq_iff.mp hev) S hS

private theorem delta_add_eq {n t : ℕ} (d : ℕ) (c : Fin t → Finset (Fin n) → F)
    (v w : Vec n) (j : Fin t) {S : Finset (Fin n)} (hS : S ∈ lowSet n d) :
    delta d c (v + w) j S = shiftVec d v (delta d c w j) S + delta d c v j S := by
  have hev : ∀ x, evalPoly d (delta d c (v + w) j) x =
      evalPoly d (fun T => shiftVec d v (delta d c w j) T + delta d c v j T) x := by
    intro x
    have hrhs : evalPoly d (fun T => shiftVec d v (delta d c w j) T + delta d c v j T) x =
        evalPoly d (shiftVec d v (delta d c w j)) x + evalPoly d (delta d c v j) x := by
      unfold evalPoly
      simp only [add_mul, Finset.sum_add_distrib]
    rw [hrhs, evalPoly_shiftVec, evalPoly_delta, evalPoly_delta, evalPoly_delta]
    have hassoc : x + (v + w) = (x + v) + w := (add_assoc x v w).symm
    rw [hassoc]
    have hcancel : evalPoly d (c j) (x + v) + evalPoly d (c j) (x + v) = 0 := z2_add_self _
    calc evalPoly d (c j) (x + v + w) + evalPoly d (c j) x
        = evalPoly d (c j) (x + v + w) + (evalPoly d (c j) (x + v) + evalPoly d (c j) (x + v)) +
            evalPoly d (c j) x := by rw [hcancel, add_zero]
      _ = (evalPoly d (c j) (x + v + w) + evalPoly d (c j) (x + v)) +
            (evalPoly d (c j) (x + v) + evalPoly d (c j) x) := by ring
  exact (evalPoly_eq_iff.mp hev) S hS

private def DegSub {n t : ℕ} (d : ℕ) (c : Fin t → Finset (Fin n) → F) (k : ℕ) : Set (Vec n) :=
  {v | ∀ j : Fin t, ∀ S ∈ lowSet n d, k < S.card → delta d c v j S = 0}

private theorem zero_mem_DegSub {n t : ℕ} (d : ℕ) (c : Fin t → Finset (Fin n) → F) (k : ℕ) :
    (0 : Vec n) ∈ DegSub d c k := by
  intro j S hS _
  exact delta_zero d c j hS

private theorem add_mem_DegSub {n t : ℕ} (d : ℕ) (c : Fin t → Finset (Fin n) → F) (k : ℕ)
    {v w : Vec n} (hv : v ∈ DegSub d c k) (hw : w ∈ DegSub d c k) :
    v + w ∈ DegSub d c k := by
  intro j S hS hk
  rw [delta_add_eq d c v w j hS]
  have h1 := (shiftVec_preserves_top d k v (hw j)).1 S hS hk
  rw [h1, hv j S hS hk, zero_add]

private theorem smul_mem_DegSub {n t : ℕ} (d : ℕ) (c : Fin t → Finset (Fin n) → F) (k : ℕ)
    (a : F) {v : Vec n} (hv : v ∈ DegSub d c k) : (fun i => a * v i) ∈ DegSub d c k := by
  rcases z2_cases a with rfl | rfl
  · have hfun : (fun i => (0 : F) * v i) = (0 : Vec n) := by funext i; exact zero_mul _
    rw [hfun]; exact zero_mem_DegSub d c k
  · have hfun : (fun i => (1 : F) * v i) = v := by funext i; exact one_mul _
    rw [hfun]; exact hv

private theorem delta_add_on_DegSub {n t : ℕ} (d : ℕ) (c : Fin t → Finset (Fin n) → F) (k : ℕ)
    {v w : Vec n} (hw : w ∈ DegSub d c k) (j : Fin t) {S : Finset (Fin n)}
    (hS : S ∈ lowSet n d) (hk : S.card = k) :
    delta d c (v + w) j S = delta d c v j S + delta d c w j S := by
  rw [delta_add_eq d c v w j hS, (shiftVec_preserves_top d k v (hw j)).2 S hS hk, add_comm]

private theorem delta_sum_on_DegSub {n t : ℕ} (d : ℕ) (c : Fin t → Finset (Fin n) → F) (k : ℕ)
    {ι : Type*} (s : Finset ι) (u : ι → F) (b : ι → Vec n) (hb : ∀ r ∈ s, b r ∈ DegSub d c k) :
    (fun i => ∑ r ∈ s, u r * b r i) ∈ DegSub d c k ∧
    ∀ j : Fin t, ∀ S ∈ lowSet n d, S.card = k →
      delta d c (fun i => ∑ r ∈ s, u r * b r i) j S = ∑ r ∈ s, u r * delta d c (b r) j S := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hfun : (fun i : Fin n => ∑ r ∈ (∅ : Finset ι), u r * b r i) = (0 : Vec n) := by
      funext i; simp
    rw [hfun]
    refine ⟨zero_mem_DegSub d c k, fun j S hS _ => ?_⟩
    rw [Finset.sum_empty]
    exact delta_zero d c j hS
  | @insert a s has ih =>
    have hba : b a ∈ DegSub d c k := hb a (Finset.mem_insert_self a s)
    have hrest := ih (fun r hr => hb r (Finset.mem_insert_of_mem hr))
    have hsplit : (fun i => ∑ r ∈ insert a s, u r * b r i) =
        (fun i => u a * b a i) + (fun i => ∑ r ∈ s, u r * b r i) := by
      funext i; simp [Finset.sum_insert has]
    rw [hsplit]
    have hua : (fun i => u a * b a i) ∈ DegSub d c k := smul_mem_DegSub d c k (u a) hba
    refine ⟨add_mem_DegSub d c k hua hrest.1, fun j S hS hk => ?_⟩
    rw [delta_add_on_DegSub d c k hrest.1 j hS hk, hrest.2 j S hS hk, Finset.sum_insert has]
    congr 1
    have hsc : delta d c (fun i => u a * b a i) j S = u a * delta d c (b a) j S := by
      rcases z2_cases (u a) with h0 | h1
      · rw [h0]
        have hfun : (fun i => (0 : F) * b a i) = (0 : Vec n) := by funext i; simp
        rw [hfun, zero_mul]
        exact delta_zero d c j hS
      · rw [h1]
        have hfun : (fun i => (1 : F) * b a i) = b a := by funext i; simp
        rw [hfun, one_mul]
    exact hsc

private theorem mem_DegSub_top {n t : ℕ} (d : ℕ) (c : Fin t → Finset (Fin n) → F) (v : Vec n) :
    v ∈ DegSub d c (min d n) := by
  intro j S hS hk
  simp only [lowSet, Finset.mem_filter, Finset.mem_univ, true_and] at hS
  have hle : S.card ≤ n := by
    calc S.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ S
      _ = n := Fintype.card_fin n
  omega

private theorem mem_DegSub_zero_iff {n t : ℕ} (d : ℕ) {f : Vec n → (Fin t → F)}
    {c : Fin t → Finset (Fin n) → F} (hf : ∀ j x, f x j = evalPoly d (c j) x)
    (v : Vec n) (a : Fin t → F) :
    (∀ x, f (x + v) = f x + a) ↔ (v ∈ DegSub d c 0 ∧ ∀ j, delta d c v j ∅ = a j) := by
  constructor
  · intro h
    have hconst : ∀ j x, evalPoly d (delta d c v j) x = evalPoly d (fun S => if S = ∅ then a j else 0) x := by
      intro j x
      rw [evalPoly_delta, ← hf j (x + v), ← hf j x]
      have hx := congrFun (h x) j
      simp only [Pi.add_apply] at hx
      rw [hx]
      have hleft : f x j + a j + f x j = a j := by
        calc f x j + a j + f x j = (f x j + f x j) + a j := by ring
          _ = a j := by rw [z2_add_self, zero_add]
      rw [hleft]
      unfold evalPoly
      rw [Finset.sum_eq_single ∅]
      · simp [monom]
      · intro S _ hne; simp [hne]
      · intro hno; exact False.elim (hno (empty_mem_lowSet n d))
    have hcoeff : ∀ j, ∀ S ∈ lowSet n d, delta d c v j S = if S = ∅ then a j else 0 :=
      fun j => evalPoly_eq_iff.mp (hconst j)
    refine ⟨?_, ?_⟩
    · intro j S hS hpos
      have hne : S ≠ ∅ := Finset.card_pos.mp hpos |>.ne_empty
      rw [hcoeff j S hS, if_neg hne]
    · intro j
      simpa using hcoeff j ∅ (empty_mem_lowSet n d)
  · rintro ⟨hv, ha⟩ x
    funext j
    simp only [Pi.add_apply]
    have hdiff : f (x + v) j + f x j = a j := by
      rw [hf j (x + v), hf j x, ← evalPoly_delta]
      unfold evalPoly
      rw [Finset.sum_eq_single ∅]
      · simp [monom, ha j]
      · intro S hS hne
        have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
        rw [hv j S hS hpos, zero_mul]
      · intro hno; exact False.elim (hno (empty_mem_lowSet n d))
    calc f (x + v) j = (f (x + v) j + f x j) + f x j := by
          calc f (x + v) j = f (x + v) j + (f x j + f x j) := by rw [z2_add_self, add_zero]
            _ = (f (x + v) j + f x j) + f x j := by ring
      _ = a j + f x j := by rw [hdiff]
      _ = f x j + a j := by ring

private def dot {n : ℕ} (a b : Vec n) : F := ∑ i : Fin n, a i * b i

private def matVec {n : ℕ} (M : Mat n) (v : Vec n) : Vec n :=
  fun i => ∑ j : Fin n, M i j * v j

private def matMul {n : ℕ} (A B : Mat n) : Mat n :=
  fun i j => ∑ k : Fin n, A i k * B k j

private def matId (n : ℕ) : Mat n :=
  fun i j => if i = j then 1 else 0

private def matTrans {n : ℕ} (A : Mat n) : Mat n :=
  fun i j => A j i

private theorem matVec_matMul {n : ℕ} (A B : Mat n) (v : Vec n) :
    matVec (matMul A B) v = matVec A (matVec B v) := by
  funext i
  unfold matVec matMul
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem matVec_id {n : ℕ} (v : Vec n) : matVec (matId n) v = v := by
  funext i
  unfold matVec matId
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hne; simp [hne.symm]
  · intro h; exact False.elim (h (Finset.mem_univ i))

private theorem matMul_trans {n : ℕ} (A B : Mat n) :
    matTrans (matMul A B) = matMul (matTrans B) (matTrans A) := by
  funext i j
  unfold matTrans matMul
  refine Finset.sum_congr rfl fun k _ => by ring

private def IsUpperEchelon {n : ℕ} (E : Mat n) : Prop :=
  (∀ p q : Fin n, q.val < p.val → E p q = 0) ∧
  (∀ p : Fin n, E p p = 0 → ∀ q : Fin n, E p q = 0)

private def IsRREF {n : ℕ} (R : Mat n) : Prop :=
  IsUpperEchelon R ∧ ∀ i p : Fin n, i ≠ p → R p p = 1 → R i p = 0

private def InRowSpan {n : ℕ} (E : Mat n) (v : Vec n) : Prop :=
  ∃ α : Vec n, v = fun q => ∑ i : Fin n, α i * E i q

private theorem zero_inRowSpan {n : ℕ} (E : Mat n) : InRowSpan E 0 :=
  ⟨0, by funext q; simp⟩

private theorem row_inRowSpan {n : ℕ} (E : Mat n) (i : Fin n) : InRowSpan E (E i) := by
  refine ⟨fun k => if k = i then 1 else 0, ?_⟩
  funext q
  rw [Finset.sum_eq_single i]
  · simp
  · intro k _ hne; simp [hne]
  · intro h; exact False.elim (h (Finset.mem_univ i))

private theorem sum_inRowSpan {n : ℕ} {E : Mat n} {u v : Vec n}
    (hu : InRowSpan E u) (hv : InRowSpan E v) : InRowSpan E (u + v) := by
  obtain ⟨α, rfl⟩ := hu
  obtain ⟨β, rfl⟩ := hv
  refine ⟨α + β, ?_⟩
  funext q
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem smul_inRowSpan {n : ℕ} {E : Mat n} (a : F) {u : Vec n}
    (hu : InRowSpan E u) : InRowSpan E (fun q => a * u q) := by
  obtain ⟨α, rfl⟩ := hu
  refine ⟨fun i => a * α i, ?_⟩
  funext q
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

private theorem dot_eq_zero_of_inRowSpan {n : ℕ} {E : Mat n} {v u : Vec n}
    (hv : InRowSpan E v) (hE : ∀ i : Fin n, dot (E i) u = 0) : dot v u = 0 := by
  obtain ⟨α, rfl⟩ := hv
  unfold dot
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  have h1 : (∑ q : Fin n, α i * E i q * u q) = α i * dot (E i) u := by
    unfold dot
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => by ring
  rw [h1, hE i, mul_zero]

private def eStep {n : ℕ} (p : Fin n) (Ew : Mat n × Vec n) : Mat n × Vec n :=
  let E := Ew.1
  let w := Ew.2
  let hit := w p
  let place := hit * (1 + E p p)
  let notPlace := 1 + place
  (fun i q => if i = p then E p q + place * w q else E i q,
   fun q => notPlace * (w q + hit * E p q))

private def insertRowFold {n : ℕ} (k : ℕ) (hk : k ≤ n) (Ew : Mat n × Vec n) : Mat n × Vec n :=
  match k with
  | 0 => Ew
  | k' + 1 => eStep ⟨k', by omega⟩ (insertRowFold k' (by omega) Ew)

private def insertRow {n : ℕ} (E : Mat n) (w : Vec n) : Mat n :=
  (insertRowFold n le_rfl (E, w)).1

private def insertRows {n : ℕ} (rows : List (Vec n)) : Mat n :=
  rows.foldl insertRow (fun _ _ => 0)

private def backStep {n : ℕ} (p : Fin n) (R : Mat n) : Mat n :=
  fun i q => if i.val < p.val then R i q + R i p * R p q else R i q

private def backFold {n : ℕ} (k : ℕ) (hk : k ≤ n) (R : Mat n) : Mat n :=
  match k with
  | 0 => R
  | k' + 1 => backFold k' (by omega) (backStep ⟨k', by omega⟩ R)

private def rref {n : ℕ} (rows : List (Vec n)) : Mat n :=
  backFold n le_rfl (insertRows rows)

private def InRowSpanPlus {n : ℕ} (E : Mat n) (w : Vec n) (v : Vec n) : Prop :=
  ∃ (a : F) (u : Vec n), InRowSpan E u ∧ v = fun q => a * w q + u q

private theorem eStep_spec {n : ℕ} (p : Fin n) (E : Mat n) (w : Vec n)
    (hE : IsUpperEchelon E) (hw : ∀ q : Fin n, q.val < p.val → w q = 0) :
    let res := eStep p (E, w)
    IsUpperEchelon res.1 ∧
    (∀ q : Fin n, q.val < p.val + 1 → res.2 q = 0) ∧
    (∀ v : Vec n, InRowSpanPlus res.1 res.2 v ↔ InRowSpanPlus E w v) := by
  dsimp only [eStep]
  generalize hwp : w p = hit
  generalize hEpp : E p p = epp
  rcases z2_cases hit with rfl | rfl <;> rcases z2_cases epp with rfl | rfl
  ·
    have hE' : (fun i q => if i = p then E p q + (0 : F) * (1 + 0) * w q else E i q) = E := by
      funext i q; split_ifs with h <;> simp [h]
    have hw'_pt : ∀ q, (1 + (0 : F) * (1 + 0)) * (w q + 0 * E p q) = w q := fun q => by simp
    have hw' : (fun q => (1 + (0 : F) * (1 + 0)) * (w q + 0 * E p q)) = w := funext hw'_pt
    rw [hE', hw']
    refine ⟨hE, fun q hq => ?_, fun _ => Iff.rfl⟩
    rw [hw'_pt q]
    by_cases hlt : q.val < p.val
    · exact hw q hlt
    · have hqp : q = p := Fin.ext (by omega)
      subst hqp; exact hwp
  ·
    have hE' : (fun i q => if i = p then E p q + (0 : F) * (1 + 1) * w q else E i q) = E := by
      funext i q; split_ifs with h <;> simp [h]
    have hw'_pt : ∀ q, (1 + (0 : F) * (1 + 1)) * (w q + 0 * E p q) = w q := fun q => by simp
    have hw' : (fun q => (1 + (0 : F) * (1 + 1)) * (w q + 0 * E p q)) = w := funext hw'_pt
    rw [hE', hw']
    refine ⟨hE, fun q hq => ?_, fun _ => Iff.rfl⟩
    rw [hw'_pt q]
    by_cases hlt : q.val < p.val
    · exact hw q hlt
    · have hqp : q = p := Fin.ext (by omega)
      subst hqp; exact hwp
  ·
    have hEp0 : ∀ q : Fin n, E p q = 0 := hE.2 p hEpp
    have hE' : (fun i q => if i = p then E p q + (1 : F) * (1 + 0) * w q else E i q) =
        fun i q => if i = p then w q else E i q := by
      funext i q; split_ifs with h
      · subst h; rw [hEp0 q]; ring
      · rfl
    have hw'_pt : ∀ q, (1 + (1 : F) * (1 + 0)) * (w q + 1 * E p q) = 0 := fun q => by
      have h2 : (1 : F) + 1 * (1 + 0) = 0 := by decide
      rw [h2, zero_mul]
    have hw' : (fun q => (1 + (1 : F) * (1 + 0)) * (w q + 1 * E p q)) = 0 := funext hw'_pt
    rw [hE', hw']
    refine ⟨?_, fun q _ => hw'_pt q, ?_⟩
    · constructor
      · intro i q hqi
        by_cases hip : i = p
        · subst hip; simpa using hw q hqi
        · simp [hip, hE.1 i q hqi]
      · intro i hii q
        by_cases hip : i = p
        · subst hip
          simp only [↓reduceIte] at hii
          rw [hwp] at hii
          exact absurd hii (by decide)
        · simp only [hip, ↓reduceIte] at hii ⊢
          exact hE.2 i hii q
    · intro v
      constructor
      · rintro ⟨a, u, ⟨α, rfl⟩, rfl⟩
        refine ⟨α p, fun q => ∑ i : Fin n, (if i = p then 0 else α i) * E i q, ⟨fun i => if i = p then 0 else α i, rfl⟩, ?_⟩
        funext q
        simp only [Pi.zero_apply, mul_zero, zero_add]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p), ← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
        simp only [↓reduceIte, zero_mul, zero_add]
        congr 1
        refine Finset.sum_congr rfl fun i hi => ?_
        have hne : i ≠ p := Finset.ne_of_mem_erase hi
        simp [hne]
      · rintro ⟨a, u, ⟨α, rfl⟩, rfl⟩
        refine ⟨0, fun q => a * w q + ∑ i : Fin n, α i * E i q, ?_, by funext q; simp⟩
        refine ⟨fun i => if i = p then a else α i, ?_⟩
        funext q
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p), ← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
        simp only [↓reduceIte]
        rw [hEp0 q, mul_zero, zero_add]
        congr 1
        refine Finset.sum_congr rfl fun i hi => ?_
        have hne : i ≠ p := Finset.ne_of_mem_erase hi
        simp [hne]
  ·
    have h11 : (1 : F) + 1 = 0 := by decide
    have hE' : (fun i q => if i = p then E p q + (1 : F) * (1 + 1) * w q else E i q) = E := by
      funext i q; split_ifs with h
      · subst h; rw [h11, mul_zero, zero_mul, add_zero]
      · rfl
    have hw'_pt : ∀ q, (1 + (1 : F) * (1 + 1)) * (w q + 1 * E p q) = w q + E p q := fun q => by
      rw [h11, mul_zero, add_zero, one_mul, one_mul]
    have hw' : (fun q => (1 + (1 : F) * (1 + 1)) * (w q + 1 * E p q)) = fun q => w q + E p q := funext hw'_pt
    rw [hE', hw']
    refine ⟨hE, ?_, ?_⟩
    · intro q hq
      rw [hw'_pt q]
      by_cases hlt : q.val < p.val
      · rw [hw q hlt, hE.1 p q hlt, add_zero]
      · have hqp : q = p := Fin.ext (by omega)
        subst hqp; rw [hwp, hEpp]; decide
    · intro v
      constructor
      · rintro ⟨a, u, hu, rfl⟩
        refine ⟨a, fun q => a * E p q + u q,
          sum_inRowSpan (smul_inRowSpan a (row_inRowSpan E p)) hu, ?_⟩
        funext q; ring
      · rintro ⟨a, u, hu, rfl⟩
        refine ⟨a, fun q => a * E p q + u q,
          sum_inRowSpan (smul_inRowSpan a (row_inRowSpan E p)) hu, ?_⟩
        funext q
        have hcancel : a * E p q + a * E p q = 0 := z2_add_self _
        calc a * w q + u q = a * w q + (a * E p q + a * E p q) + u q := by rw [hcancel, add_zero]
          _ = a * (w q + E p q) + (a * E p q + u q) := by ring

private theorem insertRowFold_spec {n : ℕ} (k : ℕ) (hk : k ≤ n) (E : Mat n) (w : Vec n)
    (hE : IsUpperEchelon E) :
    let res := insertRowFold k hk (E, w)
    IsUpperEchelon res.1 ∧
    (∀ q : Fin n, q.val < k → res.2 q = 0) ∧
    (∀ v : Vec n, InRowSpanPlus res.1 res.2 v ↔ InRowSpanPlus E w v) := by
  induction k with
  | zero =>
    exact ⟨hE, fun _ hq => absurd hq (by omega), fun _ => Iff.rfl⟩
  | succ k' ih =>
    have hprev := ih (by omega)
    have hstep := eStep_spec ⟨k', by omega⟩ (insertRowFold k' (by omega) (E, w)).1
      (insertRowFold k' (by omega) (E, w)).2 hprev.1 hprev.2.1
    refine ⟨hstep.1, hstep.2.1, fun v => (hstep.2.2 v).trans (hprev.2.2 v)⟩

private theorem insertRow_spec {n : ℕ} (E : Mat n) (w : Vec n) (hE : IsUpperEchelon E) :
    IsUpperEchelon (insertRow E w) ∧
    (∀ v : Vec n, InRowSpan (insertRow E w) v ↔ InRowSpanPlus E w v) := by
  have h := insertRowFold_spec n le_rfl E w hE
  have hw0 : (insertRowFold n le_rfl (E, w)).2 = 0 := by
    funext q; exact h.2.1 q q.isLt
  refine ⟨h.1, fun v => ?_⟩
  rw [← h.2.2 v, hw0]
  unfold InRowSpanPlus insertRow
  constructor
  · intro hv; exact ⟨0, v, hv, by funext q; simp⟩
  · rintro ⟨a, u, hu, rfl⟩
    have hfun : (fun q => a * (0 : Vec n) q + u q) = u := by funext q; simp
    simpa [hfun] using hu

private theorem isUpperEchelon_zero (n : ℕ) : IsUpperEchelon (fun _ _ : Fin n => (0 : F)) :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩

private def InListSpan {n : ℕ} : List (Vec n) → Vec n → Prop
  | [], v => v = 0
  | r :: rs, v => ∃ (a : F) (u : Vec n), InListSpan rs u ∧ v = fun q => a * r q + u q

private theorem zero_inListSpan {n : ℕ} (rows : List (Vec n)) : InListSpan rows 0 := by
  induction rows with
  | nil => rfl
  | cons r rs ih => exact ⟨0, 0, ih, by funext q; simp⟩

private theorem mem_inListSpan {n : ℕ} {rows : List (Vec n)} {r : Vec n} (hr : r ∈ rows) :
    InListSpan rows r := by
  induction rows with
  | nil => cases hr
  | cons x xs ih =>
    rcases List.mem_cons.mp hr with rfl | hmem
    · exact ⟨1, 0, zero_inListSpan xs, by funext q; simp⟩
    · exact ⟨0, r, ih hmem, by funext q; simp⟩

private theorem inListSpan_append_singleton {n : ℕ} (rows : List (Vec n)) (w v : Vec n) :
    InListSpan (rows ++ [w]) v ↔ ∃ (a : F) (u : Vec n), InListSpan rows u ∧ v = fun q => a * w q + u q := by
  induction rows generalizing v with
  | nil =>
    simp only [List.nil_append, InListSpan]
  | cons r rs ih =>
    simp only [List.cons_append, InListSpan]
    constructor
    · rintro ⟨b, u, hu, rfl⟩
      obtain ⟨a, u', hu', rfl⟩ := (ih u).mp hu
      refine ⟨a, fun q => b * r q + u' q, ⟨b, u', hu', rfl⟩, ?_⟩
      funext q; ring
    · rintro ⟨a, u, ⟨b, u', hu', rfl⟩, rfl⟩
      refine ⟨b, fun q => a * w q + u' q, (ih _).mpr ⟨a, u', hu', rfl⟩, ?_⟩
      funext q; ring

private theorem dot_eq_zero_of_inListSpan {n : ℕ} {rows : List (Vec n)} {v u : Vec n}
    (hv : InListSpan rows v) (hrows : ∀ r ∈ rows, dot r u = 0) : dot v u = 0 := by
  induction rows generalizing v with
  | nil =>
    subst hv; simp [dot]
  | cons r rs ih =>
    obtain ⟨a, w, hw, rfl⟩ := hv
    have h1 : dot (fun q => a * r q + w q) u = a * dot r u + dot w u := by
      unfold dot
      simp_rw [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    rw [h1, hrows r (List.mem_cons_self ..), mul_zero, zero_add]
    exact ih hw (fun x hx => hrows x (List.mem_cons_of_mem _ hx))

private theorem insertRows_spec {n : ℕ} (rows : List (Vec n)) :
    IsUpperEchelon (insertRows rows) ∧
    (∀ v : Vec n, InRowSpan (insertRows rows) v ↔ InListSpan rows v) := by
  induction rows using List.reverseRecOn with
  | nil =>
    refine ⟨isUpperEchelon_zero n, fun v => ?_⟩
    simp only [insertRows, List.foldl_nil, InRowSpan, InListSpan]
    constructor
    · rintro ⟨_, rfl⟩; funext q; simp
    · intro hv; subst hv; exact ⟨0, by funext q; simp⟩
  | append_singleton rs w ih =>
    have hfold : insertRows (rs ++ [w]) = insertRow (insertRows rs) w := by
      simp [insertRows, List.foldl_append]
    rw [hfold]
    have hstep := insertRow_spec (insertRows rs) w ih.1
    refine ⟨hstep.1, fun v => ?_⟩
    rw [hstep.2 v, inListSpan_append_singleton]
    unfold InRowSpanPlus
    constructor
    · rintro ⟨a, u, hu, rfl⟩; exact ⟨a, u, (ih.2 u).mp hu, rfl⟩
    · rintro ⟨a, u, hu, rfl⟩; exact ⟨a, u, (ih.2 u).mpr hu, rfl⟩

private theorem backStep_spec {n : ℕ} (p : Fin n) (R : Mat n)
    (hE : IsUpperEchelon R)
    (hhi : ∀ i j : Fin n, p.val < j.val → i ≠ j → R j j = 1 → R i j = 0) :
    IsUpperEchelon (backStep p R) ∧
    (∀ i j : Fin n, p.val ≤ j.val → i ≠ j → (backStep p R) j j = 1 → (backStep p R) i j = 0) ∧
    (∀ v : Vec n, InRowSpan (backStep p R) v ↔ InRowSpan R v) := by
  have hdiag : ∀ j : Fin n, backStep p R j j = R j j := by
    intro j
    unfold backStep
    split_ifs with hlt
    · rw [hE.1 p j hlt, mul_zero, add_zero]
    · rfl
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro i q hqi
      unfold backStep
      split_ifs with hlt
      · rw [hE.1 i q hqi, hE.1 p q (by omega), mul_zero, add_zero]
      · exact hE.1 i q hqi
    · intro i hii q
      rw [hdiag i] at hii
      unfold backStep
      split_ifs with hlt
      · rw [hE.2 i hii q, hE.2 i hii p, zero_mul, add_zero]
      · exact hE.2 i hii q
  · intro i j hj hij hjj
    rw [hdiag j] at hjj
    unfold backStep
    split_ifs with hlt
    · by_cases hjp : j = p
      · subst hjp
        rw [hjj, mul_one, z2_add_self]
      · have hgt : p.val < j.val := by omega
        rw [hhi i j hgt hij hjj, hhi p j hgt (Ne.symm hjp) hjj, mul_zero, add_zero]
    · by_cases hjp : j = p
      · subst j
        have hne_val : i.val ≠ p.val := fun h => hij (Fin.ext h)
        have hlt2 : p.val < i.val := by omega
        exact hE.1 i p hlt2
      · exact hhi i j (by omega) hij hjj
  · intro v
    constructor
    · rintro ⟨α, rfl⟩
      refine ⟨fun k => α k + if k = p then ∑ i : Fin n, if i.val < p.val then α i * R i p else 0 else 0, ?_⟩
      funext q
      have hsplit : ∀ k : Fin n,
          (α k + if k = p then ∑ i : Fin n, if i.val < p.val then α i * R i p else 0 else 0) * R k q =
          α k * R k q + if k = p then (∑ i : Fin n, if i.val < p.val then α i * R i p * R p q else 0) else 0 := by
        intro k
        rw [add_mul]
        congr 1
        split_ifs with hkp
        · subst hkp
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          split_ifs <;> ring
        · simp
      simp_rw [hsplit]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp only [Finset.mem_univ, ↓reduceIte]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold backStep
      split_ifs <;> ring
    · rintro ⟨α, rfl⟩
      refine ⟨fun k => α k + if k = p then ∑ i : Fin n, if i.val < p.val then α i * R i p else 0 else 0, ?_⟩
      funext q
      have hRp : backStep p R p q = R p q := by
        unfold backStep; simp
      have hsplit : ∀ k : Fin n,
          (α k + if k = p then ∑ i : Fin n, if i.val < p.val then α i * R i p else 0 else 0) * backStep p R k q =
          α k * backStep p R k q + if k = p then (∑ i : Fin n, if i.val < p.val then α i * R i p * R p q else 0) else 0 := by
        intro k
        rw [add_mul]
        congr 1
        split_ifs with hkp
        · subst hkp
          rw [hRp, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          split_ifs <;> ring
        · simp
      simp_rw [hsplit]
      rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp only [Finset.mem_univ, ↓reduceIte]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold backStep
      split_ifs with hlt
      · have hcancel : α i * R i p * R p q + α i * R i p * R p q = 0 := z2_add_self _
        calc α i * R i q = α i * R i q + (α i * R i p * R p q + α i * R i p * R p q) := by
              rw [hcancel, add_zero]
          _ = α i * (R i q + R i p * R p q) + α i * R i p * R p q := by ring
      · ring

private theorem backFold_spec {n : ℕ} (k : ℕ) (hk : k ≤ n) (R : Mat n)
    (hE : IsUpperEchelon R)
    (hhi : ∀ i j : Fin n, k ≤ j.val → i ≠ j → R j j = 1 → R i j = 0) :
    IsRREF (backFold k hk R) ∧
    (∀ v : Vec n, InRowSpan (backFold k hk R) v ↔ InRowSpan R v) := by
  induction k generalizing R with
  | zero =>
    exact ⟨⟨hE, fun i j hij hjj => hhi i j (Nat.zero_le _) hij hjj⟩, fun _ => Iff.rfl⟩
  | succ k' ih =>
    have hhi' : ∀ i j : Fin n, k' < j.val → i ≠ j → R j j = 1 → R i j = 0 :=
      fun i j hj => hhi i j (by omega)
    have hstep := backStep_spec ⟨k', by omega⟩ R hE hhi'
    have hrest := ih (by omega) (backStep ⟨k', by omega⟩ R) hstep.1 hstep.2.1
    exact ⟨hrest.1, fun v => (hrest.2 v).trans (hstep.2.2 v)⟩

private theorem rref_spec {n : ℕ} (rows : List (Vec n)) :
    IsRREF (rref rows) ∧ (∀ v : Vec n, InRowSpan (rref rows) v ↔ InListSpan rows v) := by
  have hins := insertRows_spec rows
  have hback := backFold_spec n le_rfl (insertRows rows) hins.1 (fun _ j hj => absurd hj (by omega))
  exact ⟨hback.1, fun v => (hback.2 v).trans (hins.2 v)⟩

private theorem rref_idem {n : ℕ} {R : Mat n} (hR : IsRREF R) : matMul R R = R := by
  funext i j
  unfold matMul
  rw [Finset.sum_eq_single i]
  · rcases z2_cases (R i i) with hRii | hRii
    · rw [hRii, zero_mul, hR.1.2 i hRii j]
    · rw [hRii, one_mul]
  · intro k _ hki
    rcases z2_cases (R k k) with hRkk | hRkk
    · rw [hR.1.2 k hRkk j, mul_zero]
    · rw [hR.2 i k (Ne.symm hki) hRkk, zero_mul]
  · intro h; exact False.elim (h (Finset.mem_univ i))

private def kerProj {n : ℕ} (R : Mat n) : Mat n :=
  fun i j => (if i = j then 1 else 0) + R i j

private theorem kerProj_mul_right {n : ℕ} {R : Mat n} (hR : IsRREF R) :
    matMul R (kerProj R) = 0 := by
  funext i j
  have h1 : matMul R (kerProj R) i j = R i j + matMul R R i j := by
    unfold matMul kerProj
    simp_rw [mul_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hkj; simp [hkj]
    · intro h; exact False.elim (h (Finset.mem_univ j))
  rw [h1, rref_idem hR, z2_add_self]
  rfl

private theorem kerProj_spec {n : ℕ} (rows : List (Vec n)) :
    let K := kerProj (rref rows)
    (∀ u : Vec n, (∀ r ∈ rows, dot r u = 0) ↔ matVec K u = u) ∧
    (∀ u : Vec n, ∀ r ∈ rows, dot r (matVec K u) = 0) := by
  dsimp only
  have hR := rref_spec rows
  set R := rref rows
  have hKu : ∀ u : Vec n, matVec (kerProj R) u = u + matVec R u := by
    intro u
    funext i
    simp only [Pi.add_apply, matVec, kerProj]
    simp_rw [add_mul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [hji.symm]
    · intro h; exact False.elim (h (Finset.mem_univ i))
  have hker_eq : ∀ u : Vec n, (∀ r ∈ rows, dot r u = 0) ↔ matVec R u = 0 := by
    intro u
    constructor
    · intro hu
      funext i
      exact dot_eq_zero_of_inListSpan ((hR.2 (R i)).mp (row_inRowSpan R i)) hu
    · intro hRu r hr
      have hdot : ∀ i : Fin n, dot (R i) u = 0 := fun i => congrFun hRu i
      exact dot_eq_zero_of_inRowSpan ((hR.2 r).mpr (mem_inListSpan hr)) hdot
  constructor
  · intro u
    rw [hker_eq u, hKu u]
    constructor
    · intro h0; rw [h0, add_zero]
    · intro heq
      funext i
      have hi := congrFun heq i
      simp only [Pi.add_apply] at hi
      have hsub := congrArg (fun z => u i + z) hi
      have h1 : u i + (u i + matVec R u i) = matVec R u i := by
        rw [← add_assoc, z2_add_self, zero_add]
      rw [h1, z2_add_self] at hsub
      exact hsub
  · intro u
    rw [hker_eq (matVec (kerProj R) u)]
    rw [← matVec_matMul, kerProj_mul_right hR.1]
    funext i; simp [matVec]

private theorem inListSpan_ofFn {n : ℕ} (M : Mat n) (v : Vec n) :
    InListSpan (List.ofFn M) v ↔ InRowSpan M v := by
  have haux : ∀ (l : List (Fin n)), l.Nodup →
      ∀ v : Vec n, InListSpan (l.map M) v ↔
        ∃ α : Vec n, (∀ i, i ∉ l → α i = 0) ∧ v = fun q => ∑ i : Fin n, α i * M i q := by
    intro l hl
    induction l with
    | nil =>
      intro v
      simp only [List.map_nil, InListSpan, List.not_mem_nil, not_false_eq_true, forall_const]
      constructor
      · intro hv; subst hv; exact ⟨0, fun _ => rfl, by funext q; simp⟩
      · rintro ⟨α, hα, rfl⟩; funext q; simp [hα]
    | cons a ls ih =>
      have hna : a ∉ ls := (List.nodup_cons.mp hl).1
      have hls : ls.Nodup := (List.nodup_cons.mp hl).2
      intro v
      simp only [List.map_cons, InListSpan]
      constructor
      · rintro ⟨c, u, hu, rfl⟩
        obtain ⟨α, hα, rfl⟩ := (ih hls u).mp hu
        refine ⟨fun i => if i = a then c else α i, ?_, ?_⟩
        · intro i hi
          rw [List.mem_cons, not_or] at hi
          simp [hi.1, hα i hi.2]
        · funext q
          dsimp only
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), ← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
          simp only [↓reduceIte, hα a hna, zero_mul, zero_add]
          congr 1
          refine Finset.sum_congr rfl fun i hi => ?_
          simp [Finset.ne_of_mem_erase hi]
      · rintro ⟨α, hα, rfl⟩
        refine ⟨α a, fun q => ∑ i : Fin n, (if i = a then 0 else α i) * M i q, ?_, ?_⟩
        · refine (ih hls _).mpr ⟨fun i => if i = a then 0 else α i, ?_, rfl⟩
          intro i hi
          by_cases hia : i = a
          · simp [hia]
          · simp [hia, hα i (by simp [hia, hi])]
        · funext q
          dsimp only
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), ← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
          simp only [↓reduceIte, zero_mul, zero_add]
          congr 1
          refine Finset.sum_congr rfl fun i hi => ?_
          simp [Finset.ne_of_mem_erase hi]
  have hofFn : List.ofFn M = (List.finRange n).map M := List.ext_getElem (by simp) (by intro i h1 h2; simp)
  rw [hofFn]
  rw [haux (List.finRange n) (List.nodup_finRange n) v]
  unfold InRowSpan
  constructor
  · rintro ⟨α, _, h⟩; exact ⟨α, h⟩
  · rintro ⟨α, h⟩; exact ⟨α, fun i hi => False.elim (hi (List.mem_finRange i)), h⟩

private theorem colProj_spec {n : ℕ} (B : Mat n) :
    let Q := rref (List.ofFn (matTrans B))
    let P := matTrans Q
    (∀ z : Vec n, matVec P (matVec P z) = matVec P z) ∧
    (∀ v : Vec n, matVec P v = v ↔ ∃ u : Vec n, v = matVec B u) := by
  dsimp only
  have hQ := rref_spec (List.ofFn (matTrans B))
  set Q := rref (List.ofFn (matTrans B))
  set P := matTrans Q
  have hPidem : matMul P P = P := by
    change matMul (matTrans Q) (matTrans Q) = matTrans Q
    rw [← matMul_trans, rref_idem hQ.1]
  have hPvec : ∀ z : Vec n, matVec P (matVec P z) = matVec P z := by
    intro z; rw [← matVec_matMul, hPidem]
  have himg : ∀ v : Vec n, (∃ w : Vec n, v = matVec P w) ↔ (∃ u : Vec n, v = matVec B u) := by
    intro v
    have h1 : (∃ w : Vec n, v = matVec P w) ↔ InRowSpan Q v := by
      constructor
      · rintro ⟨w, rfl⟩
        refine ⟨w, ?_⟩
        funext q
        unfold matVec P matTrans
        refine Finset.sum_congr rfl fun i _ => by ring
      · rintro ⟨w, rfl⟩
        refine ⟨w, ?_⟩
        funext q
        unfold matVec P matTrans
        refine Finset.sum_congr rfl fun i _ => by ring
    have h2 : (∃ u : Vec n, v = matVec B u) ↔ InRowSpan (matTrans B) v := by
      constructor
      · rintro ⟨u, rfl⟩
        refine ⟨u, ?_⟩
        funext q
        unfold matVec matTrans
        refine Finset.sum_congr rfl fun i _ => by ring
      · rintro ⟨u, rfl⟩
        refine ⟨u, ?_⟩
        funext q
        unfold matVec matTrans
        refine Finset.sum_congr rfl fun i _ => by ring
    rw [h1, h2, hQ.2 v, inListSpan_ofFn]
  refine ⟨hPvec, fun v => ?_⟩
  rw [← himg v]
  constructor
  · intro hv; exact ⟨v, hv.symm⟩
  · rintro ⟨w, rfl⟩; exact hPvec w

private def descentStep {n t : ℕ} (d k : ℕ) (enumerate : Fin (lowSet n d).card ≃ ↥(lowSet n d))
    (c : Fin t → Finset (Fin n) → F) (B : Mat n) : Mat n :=
  let rows : List (Vec n) :=
    (List.finRange t).flatMap fun j =>
      ((List.finRange (lowSet n d).card).filter fun a => (enumerate a).val.card = k).map fun a =>
        fun r : Fin n => delta d c (fun i => B i r) j (enumerate a).val
  matMul B (kerProj (rref rows))

private def descent {n t : ℕ} (d : ℕ) (enumerate : Fin (lowSet n d).card ≃ ↥(lowSet n d))
    (c : Fin t → Finset (Fin n) → F) : ℕ → Mat n
  | 0 => matId n
  | k + 1 => descentStep d (k + 1) enumerate c (descent d enumerate c k)

private def descentDown {n t : ℕ} (d : ℕ) (enumerate : Fin (lowSet n d).card ≃ ↥(lowSet n d))
    (c : Fin t → Finset (Fin n) → F) : ℕ → Mat n → Mat n
  | 0, B => B
  | k + 1, B => descentDown d enumerate c k (descentStep d (k + 1) enumerate c B)

private theorem descentStep_spec {n t : ℕ} (d k : ℕ)
    (enumerate : Fin (lowSet n d).card ≃ ↥(lowSet n d))
    (c : Fin t → Finset (Fin n) → F) (B : Mat n)
    (hB : ∀ v : Vec n, (∃ u : Vec n, v = matVec B u) ↔ v ∈ DegSub d c (k + 1)) :
    ∀ v : Vec n, (∃ u : Vec n, v = matVec (descentStep d (k + 1) enumerate c B) u) ↔
      v ∈ DegSub d c k := by
  let rows : List (Vec n) :=
    (List.finRange t).flatMap fun j =>
      ((List.finRange (lowSet n d).card).filter fun a => (enumerate a).val.card = k + 1).map fun a =>
        fun r : Fin n => delta d c (fun i => B i r) j (enumerate a).val
  have hcol : ∀ r : Fin n, (fun i => B i r) ∈ DegSub d c (k + 1) := by
    intro r
    rw [← hB]
    refine ⟨fun i => if i = r then 1 else 0, ?_⟩
    funext i
    unfold matVec
    rw [Finset.sum_eq_single r]
    · simp
    · intro j _ hjr; simp [hjr]
    · intro h; exact False.elim (h (Finset.mem_univ r))
  have hker_iff : ∀ u : Vec n,
      (∀ row ∈ rows, dot row u = 0) ↔ matVec B u ∈ DegSub d c k := by
    intro u
    have hBu_eq : matVec B u = fun i => ∑ r ∈ (Finset.univ : Finset (Fin n)), u r * B i r := by
      funext i; unfold matVec
      refine Finset.sum_congr rfl fun r _ => by ring
    have hsum := delta_sum_on_DegSub d c (k + 1) Finset.univ u (fun r i => B i r) (fun r _ => hcol r)
    rw [← hBu_eq] at hsum
    have hdot_eq : ∀ (j : Fin t) (a : Fin (lowSet n d).card), (enumerate a).val.card = k + 1 →
        dot (fun r => delta d c (fun i => B i r) j (enumerate a).val) u =
          delta d c (matVec B u) j (enumerate a).val := by
      intro j a ha
      rw [hsum.2 j (enumerate a).val (enumerate a).property ha]
      unfold dot
      refine Finset.sum_congr rfl fun r _ => by ring
    constructor
    · intro hrow j S hS hk
      by_cases hgt : k + 1 < S.card
      · exact hsum.1 j S hS hgt
      · have heq : S.card = k + 1 := by omega
        let a := enumerate.symm ⟨S, hS⟩
        have haS : (enumerate a).val = S := by simp [a]
        have ha_card : (enumerate a).val.card = k + 1 := by rw [haS]; exact heq
        have hmem : (fun r => delta d c (fun i => B i r) j (enumerate a).val) ∈ rows := by
          simp only [rows, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_finRange,
            true_and, decide_eq_true_eq]
          exact ⟨j, a, ha_card, rfl⟩
        have h0 := hrow _ hmem
        rw [hdot_eq j a ha_card, haS] at h0
        exact h0
    · intro hmem row hrow
      simp only [rows, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_finRange,
        true_and, decide_eq_true_eq] at hrow
      obtain ⟨j, a, ha_card, rfl⟩ := hrow
      rw [hdot_eq j a ha_card]
      exact hmem j (enumerate a).val (enumerate a).property (by omega)
  have hK := kerProj_spec rows
  intro v
  unfold descentStep
  change (∃ u : Vec n, v = matVec (matMul B (kerProj (rref rows))) u) ↔ _
  constructor
  · rintro ⟨u, rfl⟩
    rw [matVec_matMul]
    exact (hker_iff (matVec (kerProj (rref rows)) u)).mp (hK.2 u)
  · intro hv
    have hv_hi : v ∈ DegSub d c (k + 1) := fun j S hS hk => hv j S hS (by omega)
    obtain ⟨u, rfl⟩ := (hB v).mpr hv_hi
    have hu_ker : ∀ row ∈ rows, dot row u = 0 := (hker_iff u).mpr hv
    have hKu : matVec (kerProj (rref rows)) u = u := (hK.1 u).mp hu_ker
    refine ⟨u, ?_⟩
    rw [matVec_matMul, hKu]

private theorem descentDown_spec {n t : ℕ} (d : ℕ)
    (enumerate : Fin (lowSet n d).card ≃ ↥(lowSet n d))
    (c : Fin t → Finset (Fin n) → F) :
    ∀ (k : ℕ) (B : Mat n),
      (∀ v : Vec n, (∃ u : Vec n, v = matVec B u) ↔ v ∈ DegSub d c k) →
      ∀ v : Vec n, (∃ u : Vec n, v = matVec (descentDown d enumerate c k B) u) ↔
        v ∈ DegSub d c 0 := by
  intro k
  induction k with
  | zero => intro B hB; exact hB
  | succ k' ih =>
    intro B hB
    exact ih (descentStep d (k' + 1) enumerate c B) (descentStep_spec d k' enumerate c B hB)

private theorem pure_algo_spec {n t d : ℕ}
    (enumerate : Fin (lowSet n d).card ≃ ↥(lowSet n d))
    (f : Vec n → (Fin t → F))
    (hf_poly : ∀ j : Fin t, ∃ c : Finset (Fin n) → F, ∀ x : Vec n, f x j = evalPoly d c x) :
    let c : Fin t → Finset (Fin n) → F := fun j => mobius (fun T => f (ind T) j)
    let B0 : Mat n := descentDown d enumerate c (min d n) (matId n)
    let P : Mat n := matTrans (rref (List.ofFn (matTrans B0)))
    let L : Fin t → Fin n → F := fun j i => delta d c (fun row => P row i) j ∅
    (∀ z : Vec n, matVec P (matVec P z) = matVec P z) ∧
    (∀ (v : Vec n) (a : Fin t → F),
      (∀ x : Vec n, f (x + v) = f x + a) ↔
        matVec P v = v ∧ (fun j => ∑ i : Fin n, L j i * v i) = a) := by
  dsimp only
  set c : Fin t → Finset (Fin n) → F := fun j => mobius (fun T => f (ind T) j)
  have hf_c : ∀ j x, f x j = evalPoly d (c j) x := by
    intro j x
    obtain ⟨c0, hc0⟩ := hf_poly j
    rw [hc0 x]
    refine Finset.sum_congr rfl fun S hS => ?_
    rw [← mobius_recover hc0 hS]
  set B0 : Mat n := descentDown d enumerate c (min d n) (matId n)
  have hB0 : ∀ v : Vec n, (∃ u : Vec n, v = matVec B0 u) ↔ v ∈ DegSub d c 0 := by
    apply descentDown_spec d enumerate c (min d n) (matId n)
    intro v
    constructor
    · intro _; exact mem_DegSub_top d c v
    · intro _; exact ⟨v, (matVec_id v).symm⟩
  have hcolP := colProj_spec B0
  set P : Mat n := matTrans (rref (List.ofFn (matTrans B0)))
  have hPv_iff : ∀ v : Vec n, matVec P v = v ↔ v ∈ DegSub d c 0 :=
    fun v => (hcolP.2 v).trans (hB0 v)
  have hPcol_mem : ∀ i : Fin n, (fun row => P row i) ∈ DegSub d c 0 := by
    intro i
    rw [← hPv_iff]
    have hPi : (fun row => P row i) = matVec P (fun k => if k = i then 1 else 0) := by
      funext row
      unfold matVec
      rw [Finset.sum_eq_single i]
      · simp
      · intro k _ hki; simp [hki]
      · intro h; exact False.elim (h (Finset.mem_univ i))
    rw [hPi, hcolP.1]
  refine ⟨hcolP.1, fun v a => ?_⟩
  rw [mem_DegSub_zero_iff d hf_c v a, ← hPv_iff v]
  constructor
  · rintro ⟨hPv, hdel⟩
    refine ⟨hPv, ?_⟩
    funext j
    have hsum := (delta_sum_on_DegSub d c 0 Finset.univ v (fun i row => P row i)
      (fun i _ => hPcol_mem i)).2 j ∅ (empty_mem_lowSet n d) rfl
    have hvec : (fun row => ∑ i ∈ (Finset.univ : Finset (Fin n)), v i * P row i) = v := by
      conv_rhs => rw [← hPv]
      funext row
      unfold matVec
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [hvec] at hsum
    calc ∑ i : Fin n, delta d c (fun row => P row i) j ∅ * v i
        = ∑ i : Fin n, v i * delta d c (fun row => P row i) j ∅ :=
          Finset.sum_congr rfl fun i _ => by ring
      _ = delta d c v j ∅ := hsum.symm
      _ = a j := hdel j
  · rintro ⟨hPv, hL⟩
    refine ⟨hPv, fun j => ?_⟩
    have hsum := (delta_sum_on_DegSub d c 0 Finset.univ v (fun i row => P row i)
      (fun i _ => hPcol_mem i)).2 j ∅ (empty_mem_lowSet n d) rfl
    have hvec : (fun row => ∑ i ∈ (Finset.univ : Finset (Fin n)), v i * P row i) = v := by
      conv_rhs => rw [← hPv]
      funext row
      unfold matVec
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [hvec] at hsum
    rw [hsum, ← congrFun hL j]
    exact Finset.sum_congr rfl fun i _ => by ring

private def ValidG (inputs : ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) ∧
  (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < inputs + j)

private def Extends (gs1 gs2 : List Gate) : Prop :=
  ∃ extra, gs2 = gs1 ++ extra

private theorem extends_refl (gs : List Gate) : Extends gs gs :=
  ⟨[], by simp⟩

private theorem extends_trans {gs1 gs2 gs3 : List Gate}
    (h12 : Extends gs1 gs2) (h23 : Extends gs2 gs3) : Extends gs1 gs3 := by
  obtain ⟨e1, rfl⟩ := h12
  obtain ⟨e2, rfl⟩ := h23
  exact ⟨e1 ++ e2, by simp [List.append_assoc]⟩

private theorem extends_len {gs1 gs2 : List Gate} (h : Extends gs1 gs2) :
    gs1.length ≤ gs2.length := by
  obtain ⟨e, rfl⟩ := h; simp

private def wiresG (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

private def evalW (gs : List Gate) (x : List Bool) (w : ℕ) : F :=
  b2z ((wiresG gs x).getD w false)

private theorem wiresG_len (gs : List Gate) (x : List Bool) :
    (wiresG gs x).length = x.length + gs.length := by
  unfold wiresG
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

private theorem getD_append_left' {α : Type} (l1 l2 : List α) (d : α) {i : ℕ} (hi : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

private theorem getD_snoc' {α : Type} (l : List α) (v d : α) (i : ℕ) :
    (l ++ [v]).getD i d = if i < l.length then l.getD i d else if i = l.length then v else d := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (by simp; omega)]; rfl

private theorem wiresG_append (gs1 gs2 : List Gate) (x : List Bool) :
    wiresG (gs1 ++ gs2) x = wiresG gs2 (wiresG gs1 x) := by
  unfold wiresG; exact List.foldl_append

private theorem wiresG_prefix (gs : List Gate) (x : List Bool) :
    ∃ extra, wiresG gs x = x ++ extra := by
  induction gs generalizing x with
  | nil => exact ⟨[], by simp [wiresG]⟩
  | cons g gs ih =>
    simp only [wiresG, List.foldl_cons]
    obtain ⟨extra, hex⟩ := ih (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])
    refine ⟨[g.op.eval (g.inputs.map fun i => x.getD i false)] ++ extra, ?_⟩
    rw [← List.append_assoc]
    exact hex

private theorem evalW_extends {inputs : ℕ} {gs1 gs2 : List Gate} (h : Extends gs1 gs2)
    {x : List Bool} (hx : x.length = inputs) {w : ℕ} (hw : w < inputs + gs1.length) :
    evalW gs2 x w = evalW gs1 x w := by
  obtain ⟨extra, rfl⟩ := h
  unfold evalW
  rw [wiresG_append]
  obtain ⟨ex, hex⟩ := wiresG_prefix extra (wiresG gs1 x)
  rw [hex, getD_append_left']
  rw [wiresG_len, hx]
  exact hw

private theorem validG_append_one {inputs : ℕ} {gs : List Gate} (hV : ValidG inputs gs)
    (g : Gate)
    (hg_fan : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hg_back : ∀ i ∈ g.inputs, i < inputs + gs.length) :
    ValidG inputs (gs ++ [g]) := by
  constructor
  · intro g' hg'
    rcases List.mem_append.mp hg' with h1 | h2
    · exact hV.1 g' h1
    · rw [List.mem_singleton.mp h2]; exact hg_fan
  · intro j hj i hi
    simp only [List.length_append, List.length_cons, List.length_nil] at hj
    rw [getD_snoc'] at hi
    by_cases hlt : j < gs.length
    · rw [if_pos hlt] at hi
      exact hV.2 j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      simp only [lt_self_iff_false, ↓reduceIte] at hi
      exact hg_back i hi

private theorem evalW_append_one {inputs : ℕ} (gs : List Gate) (g : Gate)
    {x : List Bool} (hx : x.length = inputs) :
    evalW (gs ++ [g]) x (inputs + gs.length) =
      b2z (g.op.eval (g.inputs.map fun i => (wiresG gs x).getD i false)) := by
  unfold evalW
  rw [wiresG_append]
  change b2z ((wiresG gs x ++ [g.op.eval (g.inputs.map fun i => (wiresG gs x).getD i false)]).getD (inputs + gs.length) false) = _
  rw [getD_snoc']
  have hlen : (wiresG gs x).length = inputs + gs.length := by rw [wiresG_len, hx]
  rw [hlen, if_neg (lt_irrefl _), if_pos rfl]

private def mkNot (inputs : ℕ) (gs : List Gate) (a : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨GateOp.not, [a]⟩], inputs + gs.length)

private def mkAnd (inputs : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨GateOp.and, [a, b]⟩], inputs + gs.length)

private def mkOr (inputs : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  (gs ++ [⟨GateOp.or, [a, b]⟩], inputs + gs.length)

private def mkXor (inputs : ℕ) (gs : List Gate) (a b : ℕ) : List Gate × ℕ :=
  let r1 := mkAnd inputs gs a b
  let r2 := mkNot inputs r1.1 r1.2
  let r3 := mkOr inputs r2.1 a b
  mkAnd inputs r3.1 r3.2 r2.2

private theorem mkNot_spec {inputs : ℕ} {gs : List Gate} (hV : ValidG inputs gs)
    {a : ℕ} (ha : a < inputs + gs.length) :
    let res := mkNot inputs gs a
    ValidG inputs res.1 ∧ Extends gs res.1 ∧ res.1.length = gs.length + 1 ∧
    res.2 < inputs + res.1.length ∧
    ∀ x : List Bool, x.length = inputs → evalW res.1 x res.2 = 1 + evalW gs x a := by
  dsimp only [mkNot]
  refine ⟨validG_append_one hV _ ⟨by simp, by simp⟩ (by simpa), ⟨[_], rfl⟩, by simp, by simp, ?_⟩
  intro x hx
  rw [evalW_append_one gs _ hx]
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
  exact b2z_not _

private theorem mkAnd_spec {inputs : ℕ} {gs : List Gate} (hV : ValidG inputs gs)
    {a b : ℕ} (ha : a < inputs + gs.length) (hb : b < inputs + gs.length) :
    let res := mkAnd inputs gs a b
    ValidG inputs res.1 ∧ Extends gs res.1 ∧ res.1.length = gs.length + 1 ∧
    res.2 < inputs + res.1.length ∧
    ∀ x : List Bool, x.length = inputs → evalW res.1 x res.2 = evalW gs x a * evalW gs x b := by
  dsimp only [mkAnd]
  refine ⟨validG_append_one hV _ ⟨by simp, by simp⟩ (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption),
    ⟨[_], rfl⟩, by simp, by simp, ?_⟩
  intro x hx
  rw [evalW_append_one gs _ hx]
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
  exact b2z_and _ _

private theorem mkOr_spec {inputs : ℕ} {gs : List Gate} (hV : ValidG inputs gs)
    {a b : ℕ} (ha : a < inputs + gs.length) (hb : b < inputs + gs.length) :
    let res := mkOr inputs gs a b
    ValidG inputs res.1 ∧ Extends gs res.1 ∧ res.1.length = gs.length + 1 ∧
    res.2 < inputs + res.1.length ∧
    ∀ x : List Bool, x.length = inputs →
      (wiresG res.1 x).getD res.2 false = ((wiresG gs x).getD a false || (wiresG gs x).getD b false) := by
  dsimp only [mkOr]
  refine ⟨validG_append_one hV _ ⟨by simp, by simp⟩ (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption),
    ⟨[_], rfl⟩, by simp, by simp, ?_⟩
  intro x hx
  rw [wiresG_append]
  change (wiresG gs x ++ [GateOp.eval GateOp.or ([a, b].map fun i => (wiresG gs x).getD i false)]).getD (inputs + gs.length) false = _
  rw [getD_snoc']
  have hlen : (wiresG gs x).length = inputs + gs.length := by rw [wiresG_len, hx]
  rw [hlen, if_neg (lt_irrefl _), if_pos rfl]
  simp [GateOp.eval]

private theorem mkXor_spec {inputs : ℕ} {gs : List Gate} (hV : ValidG inputs gs)
    {a b : ℕ} (ha : a < inputs + gs.length) (hb : b < inputs + gs.length) :
    let res := mkXor inputs gs a b
    ValidG inputs res.1 ∧ Extends gs res.1 ∧ res.1.length = gs.length + 4 ∧
    res.2 < inputs + res.1.length ∧
    ∀ x : List Bool, x.length = inputs → evalW res.1 x res.2 = evalW gs x a + evalW gs x b := by
  unfold mkXor
  have h1 := mkAnd_spec hV ha hb
  set gs1 := (mkAnd inputs gs a b).1
  set wAnd := (mkAnd inputs gs a b).2
  have h2 := mkNot_spec h1.1 h1.2.2.2.1
  set gs2 := (mkNot inputs gs1 wAnd).1
  set wNand := (mkNot inputs gs1 wAnd).2
  have hl1 : gs1.length = gs.length + 1 := h1.2.2.1
  have hl2 : gs2.length = gs1.length + 1 := h2.2.2.1
  have ha2 : a < inputs + gs2.length := by omega
  have hb2 : b < inputs + gs2.length := by omega
  have h3 := mkOr_spec h2.1 ha2 hb2
  set gs3 := (mkOr inputs gs2 a b).1
  set wOr := (mkOr inputs gs2 a b).2
  have hl3 : gs3.length = gs2.length + 1 := h3.2.2.1
  have hwN2 : wNand < inputs + gs2.length := h2.2.2.2.1
  have hwN3 : wNand < inputs + gs3.length := by omega
  have h4 := mkAnd_spec h3.1 h3.2.2.2.1 hwN3
  set gs4 := (mkAnd inputs gs3 wOr wNand).1
  set wOut := (mkAnd inputs gs3 wOr wNand).2
  have hl4 : gs4.length = gs3.length + 1 := h4.2.2.1
  have hext12 : Extends gs gs2 := extends_trans h1.2.1 h2.2.1
  have hext13 : Extends gs gs3 := extends_trans hext12 h3.2.1
  have hext14 : Extends gs gs4 := extends_trans hext13 h4.2.1
  refine ⟨h4.1, hext14, by change gs4.length = gs.length + 4; omega, h4.2.2.2.1, ?_⟩
  intro x hx
  have h4e := h4.2.2.2.2 x hx
  have h3e := h3.2.2.2.2 x hx
  have h2e := h2.2.2.2.2 x hx
  have h1e := h1.2.2.2.2 x hx
  have hNand3 : evalW gs3 x wNand = evalW gs2 x wNand := evalW_extends h3.2.1 hx h2.2.2.2.1
  have hwa2 : (wiresG gs2 x).getD a false = (wiresG gs x).getD a false := by
    have := evalW_extends hext12 hx ha
    unfold evalW at this
    revert this
    cases (wiresG gs2 x).getD a false <;> cases (wiresG gs x).getD a false <;> decide
  have hwb2 : (wiresG gs2 x).getD b false = (wiresG gs x).getD b false := by
    have := evalW_extends hext12 hx hb
    unfold evalW at this
    revert this
    cases (wiresG gs2 x).getD b false <;> cases (wiresG gs x).getD b false <;> decide
  rw [h4e, hNand3, h2e, h1e]
  unfold evalW at h3e ⊢
  rw [h3e, hwa2, hwb2]
  generalize (wiresG gs x).getD a false = ba
  generalize (wiresG gs x).getD b false = bb
  cases ba <;> cases bb <;> decide

private def foldFin {α : Type} (n : ℕ) (step : Fin n → α → α) (init : α) : α :=
  (List.finRange n).foldl (fun s i => step i s) init

private def cMobiusStep {n d : ℕ} (inputs : ℕ)
    (enumerate : Fin (lowSet n d).card ≃ ↥(lowSet n d))
    (coord : Fin n) (st : List Gate × (Fin (lowSet n d).card → ℕ)) :
    List Gate × (Fin (lowSet n d).card → ℕ) :=
  let oldArr := st.2
  foldFin (lowSet n d).card (fun a cur =>
    let S := (enumerate a).val
    if h : coord ∈ S then
      let S' : ↥(lowSet n d) := ⟨S.erase coord, mem_lowSet_of_subset (enumerate a).property (Finset.erase_subset coord S)⟩
      let a' := enumerate.symm S'
      let (gs', w) := mkXor inputs cur.1 (oldArr a) (oldArr a')
      (gs', fun b => if b = a then w else cur.2 b)
    else cur) (st.1, oldArr)

private theorem cMobiusStep_spec {n d : ℕ} {inputs : ℕ}
    (enumerate : Fin (lowSet n d).card ≃ ↥(lowSet n d))
    (coord : Fin n) (gs : List Gate) (arr : Fin (lowSet n d).card → ℕ)
    (hV : ValidG inputs gs) (harr : ∀ a, arr a < inputs + gs.length) :
    let res := cMobiusStep inputs enumerate coord (gs, arr)
    ValidG inputs res.1 ∧ Extends gs res.1 ∧
    res.1.length ≤ gs.length + 4 * (lowSet n d).card ∧
    (∀ a, res.2 a < inputs + res.1.length) ∧
    ∀ (x : List Bool) (_hx : x.length = inputs) (g : Finset (Fin n) → F),
      (∀ a, evalW gs x (arr a) = g (enumerate a).val) →
      ∀ a, evalW res.1 x (res.2 a) = mobiusStep coord g (enumerate a).val := by
  have haux : ∀ (l : List (Fin (lowSet n d).card)), l.Nodup →
      let res := l.foldl (fun cur a =>
        let S := (enumerate a).val
        if h : coord ∈ S then
          let S' : ↥(lowSet n d) := ⟨S.erase coord, mem_lowSet_of_subset (enumerate a).property (Finset.erase_subset coord S)⟩
          let a' := enumerate.symm S'
          let (gs', w) := mkXor inputs cur.1 (arr a) (arr a')
          (gs', fun b => if b = a then w else cur.2 b)
        else cur) (gs, arr)
      ValidG inputs res.1 ∧ Extends gs res.1 ∧
      res.1.length ≤ gs.length + 4 * l.length ∧
      (∀ a, res.2 a < inputs + res.1.length) ∧
      ∀ (x : List Bool) (_hx : x.length = inputs) (g : Finset (Fin n) → F),
        (∀ a, evalW gs x (arr a) = g (enumerate a).val) →
        ∀ a, evalW res.1 x (res.2 a) = if a ∈ l then mobiusStep coord g (enumerate a).val else g (enumerate a).val := by
    intro l hl
    induction l using List.reverseRecOn with
    | nil =>
      refine ⟨hV, extends_refl gs, by simp, harr, fun x _ g hg a => by simp [hg a]⟩
    | append_singleton ls a ih =>
      have hls : ls.Nodup := (List.nodup_append.mp hl).1
      have hna : a ∉ ls := by
        intro hmem
        exact (List.nodup_append.mp hl).2.2 a hmem a (List.mem_singleton_self a) rfl
      have hprev := ih hls
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append,
        List.length_cons, List.length_nil]
      set cur := ls.foldl (fun cur a =>
        let S := (enumerate a).val
        if h : coord ∈ S then
          let S' : ↥(lowSet n d) := ⟨S.erase coord, mem_lowSet_of_subset (enumerate a).property (Finset.erase_subset coord S)⟩
          let a' := enumerate.symm S'
          let (gs', w) := mkXor inputs cur.1 (arr a) (arr a')
          (gs', fun b => if b = a then w else cur.2 b)
        else cur) (gs, arr)
      by_cases hcoord : coord ∈ (enumerate a).val
      · simp only [hcoord, ↓reduceDIte]
        set S' : ↥(lowSet n d) := ⟨(enumerate a).val.erase coord,
          mem_lowSet_of_subset (enumerate a).property (Finset.erase_subset coord _)⟩
        set a' := enumerate.symm S'
        have ha_cur : arr a < inputs + cur.1.length := lt_of_lt_of_le (harr a) (Nat.add_le_add_left (extends_len hprev.2.1) _)
        have ha'_cur : arr a' < inputs + cur.1.length := lt_of_lt_of_le (harr a') (Nat.add_le_add_left (extends_len hprev.2.1) _)
        have hxor := mkXor_spec hprev.1 ha_cur ha'_cur
        set gs' := (mkXor inputs cur.1 (arr a) (arr a')).1
        set w := (mkXor inputs cur.1 (arr a) (arr a')).2
        have hl_prev : cur.1.length ≤ gs.length + 4 * ls.length := hprev.2.2.1
        have hl_xor : gs'.length = cur.1.length + 4 := hxor.2.2.1
        refine ⟨hxor.1, extends_trans hprev.2.1 hxor.2.1, by change gs'.length ≤ _; omega, ?_, ?_⟩
        · intro b
          by_cases hba : b = a
          · subst hba; simpa using hxor.2.2.2.1
          · simp only [hba, ↓reduceIte]
            exact lt_of_lt_of_le (hprev.2.2.2.1 b) (Nat.add_le_add_left (extends_len hxor.2.1) _)
        · intro x hx g hg b
          by_cases hba : b = a
          · subst hba
            simp only [↓reduceIte, List.mem_append, List.mem_singleton, or_true]
            rw [hxor.2.2.2.2 x hx, evalW_extends hprev.2.1 hx (harr b),
              evalW_extends hprev.2.1 hx (harr a'), hg b, hg a']
            have hS' : (enumerate a').val = (enumerate b).val.erase coord := by simp [a', S']
            rw [hS']
            simp [mobiusStep, hcoord]
          · simp only [hba, ↓reduceIte, List.mem_append, List.mem_singleton, or_false]
            rw [evalW_extends hxor.2.1 hx (hprev.2.2.2.1 b)]
            exact hprev.2.2.2.2 x hx g hg b
      · simp only [hcoord, ↓reduceDIte]
        refine ⟨hprev.1, hprev.2.1, by omega, hprev.2.2.2.1, ?_⟩
        intro x hx g hg b
        by_cases hba : b = a
        · subst hba
          simp only [List.mem_append, List.mem_singleton, or_true, ↓reduceIte]
          rw [hprev.2.2.2.2 x hx g hg b, if_neg hna]
          simp [mobiusStep, hcoord]
        · simp only [List.mem_append, List.mem_singleton, hba, or_false]
          exact hprev.2.2.2.2 x hx g hg b
  have h := haux (List.finRange (lowSet n d).card) (List.nodup_finRange _)
  simpa [cMobiusStep, foldFin, List.mem_finRange] using h

private def cMobiusOne {n d : ℕ} (inputs : ℕ)
    (enumerate : Fin (lowSet n d).card ≃ ↥(lowSet n d))
    (gs : List Gate) (init : Fin (lowSet n d).card → ℕ) :
    List Gate × (Fin (lowSet n d).card → ℕ) :=
  foldFin n (fun coord cur => cMobiusStep inputs enumerate coord cur) (gs, init)

private theorem cMobiusOne_spec {n d : ℕ} {inputs : ℕ}
    (enumerate : Fin (lowSet n d).card ≃ ↥(lowSet n d))
    (gs : List Gate) (init : Fin (lowSet n d).card → ℕ)
    (hV : ValidG inputs gs) (hinit : ∀ a, init a < inputs + gs.length) :
    let res := cMobiusOne inputs enumerate gs init
    ValidG inputs res.1 ∧ Extends gs res.1 ∧
    res.1.length ≤ gs.length + 4 * n * (lowSet n d).card ∧
    (∀ a, res.2 a < inputs + res.1.length) ∧
    ∀ (x : List Bool) (_hx : x.length = inputs) (g : Finset (Fin n) → F),
      (∀ a, evalW gs x (init a) = g (enumerate a).val) →
      ∀ a, evalW res.1 x (res.2 a) = mobius g (enumerate a).val := by
  have haux : ∀ (l : List (Fin n)),
      let res := l.foldl (fun cur coord => cMobiusStep inputs enumerate coord cur) (gs, init)
      ValidG inputs res.1 ∧ Extends gs res.1 ∧
      res.1.length ≤ gs.length + 4 * l.length * (lowSet n d).card ∧
      (∀ a, res.2 a < inputs + res.1.length) ∧
      ∀ (x : List Bool) (_hx : x.length = inputs) (g : Finset (Fin n) → F),
        (∀ a, evalW gs x (init a) = g (enumerate a).val) →
        ∀ a, evalW res.1 x (res.2 a) = mobiusFold l g (enumerate a).val := by
    intro l
    induction l using List.reverseRecOn with
    | nil =>
      refine ⟨hV, extends_refl gs, by simp, hinit, fun x _ g hg a => by simpa [mobiusFold] using hg a⟩
    | append_singleton ls coord ih =>
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append,
        List.length_cons, List.length_nil]
      set cur := ls.foldl (fun cur coord => cMobiusStep inputs enumerate coord cur) (gs, init)
      have hstep := cMobiusStep_spec enumerate coord cur.1 cur.2 ih.1 ih.2.2.2.1
      refine ⟨hstep.1, extends_trans ih.2.1 hstep.2.1, ?_, hstep.2.2.2.1, ?_⟩
      · have h1 := ih.2.2.1
        have h2 := hstep.2.2.1
        nlinarith
      · intro x hx g hg a
        have hfold : mobiusFold (ls ++ [coord]) g = mobiusStep coord (mobiusFold ls g) := by
          simp [mobiusFold, List.foldl_append]
        rw [hfold]
        exact hstep.2.2.2.2 x hx (mobiusFold ls g) (ih.2.2.2.2 x hx g hg) a
  have h := haux (List.finRange n)
  simpa [cMobiusOne, foldFin, mobius] using h

private def cMobiusAll {n t d : ℕ} (inputs : ℕ)
    (enumerate : Fin (lowSet n d).card ≃ ↥(lowSet n d))
    (gs : List Gate) (inW : Fin t → Fin (lowSet n d).card → ℕ) :
    List Gate × (Fin t → Fin (lowSet n d).card → ℕ) :=
  foldFin t (fun j cur =>
    let (gs', arr') := cMobiusOne inputs enumerate cur.1 (inW j)
    (gs', fun k => if k = j then arr' else cur.2 k)) (gs, inW)

private theorem cMobiusAll_spec {n t d : ℕ} {inputs : ℕ}
    (enumerate : Fin (lowSet n d).card ≃ ↥(lowSet n d))
    (gs : List Gate) (inW : Fin t → Fin (lowSet n d).card → ℕ)
    (hV : ValidG inputs gs) (hin : ∀ j a, inW j a < inputs + gs.length) :
    let res := cMobiusAll inputs enumerate gs inW
    ValidG inputs res.1 ∧ Extends gs res.1 ∧
    res.1.length ≤ gs.length + 4 * t * n * (lowSet n d).card ∧
    (∀ j a, res.2 j a < inputs + res.1.length) ∧
    ∀ (x : List Bool) (_hx : x.length = inputs) (g : Fin t → Finset (Fin n) → F),
      (∀ j a, evalW gs x (inW j a) = g j (enumerate a).val) →
      ∀ j a, evalW res.1 x (res.2 j a) = mobius (g j) (enumerate a).val := by
  have haux : ∀ (l : List (Fin t)), l.Nodup →
      let res := l.foldl (fun cur j =>
        let (gs', arr') := cMobiusOne inputs enumerate cur.1 (inW j)
        (gs', fun k => if k = j then arr' else cur.2 k)) (gs, inW)
      ValidG inputs res.1 ∧ Extends gs res.1 ∧
      res.1.length ≤ gs.length + 4 * l.length * n * (lowSet n d).card ∧
      (∀ j a, res.2 j a < inputs + res.1.length) ∧
      ∀ (x : List Bool) (_hx : x.length = inputs) (g : Fin t → Finset (Fin n) → F),
        (∀ j a, evalW gs x (inW j a) = g j (enumerate a).val) →
        ∀ j ∈ l, ∀ a, evalW res.1 x (res.2 j a) = mobius (g j) (enumerate a).val := by
    intro l hl
    induction l using List.reverseRecOn with
    | nil =>
      refine ⟨hV, extends_refl gs, by simp, hin, fun _ _ _ _ _ hj => by cases hj⟩
    | append_singleton ls j ih =>
      have hls : ls.Nodup := (List.nodup_append.mp hl).1
      have hprev := ih hls
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append,
        List.length_cons, List.length_nil]
      set cur := ls.foldl (fun cur j =>
        let (gs', arr') := cMobiusOne inputs enumerate cur.1 (inW j)
        (gs', fun k => if k = j then arr' else cur.2 k)) (gs, inW)
      have hinj : ∀ a, inW j a < inputs + cur.1.length :=
        fun a => lt_of_lt_of_le (hin j a) (Nat.add_le_add_left (extends_len hprev.2.1) _)
      have hstep := cMobiusOne_spec enumerate cur.1 (inW j) hprev.1 hinj
      refine ⟨hstep.1, extends_trans hprev.2.1 hstep.2.1, ?_, ?_, ?_⟩
      · have h1 := hprev.2.2.1
        have h2 := hstep.2.2.1
        nlinarith
      · intro k a
        by_cases hkj : k = j
        · subst hkj; simpa using hstep.2.2.2.1 a
        · simp only [hkj, ↓reduceIte]
          exact lt_of_lt_of_le (hprev.2.2.2.1 k a) (Nat.add_le_add_left (extends_len hstep.2.1) _)
      · intro x hx g hg k hk a
        by_cases hkj : k = j
        · subst hkj
          simp only [↓reduceIte]
          exact hstep.2.2.2.2 x hx (g k) (fun b => by rw [evalW_extends hprev.2.1 hx (hin k b), hg k b]) a
        · simp only [hkj, ↓reduceIte]
          rw [evalW_extends hstep.2.1 hx (hprev.2.2.2.1 k a)]
          have hkls : k ∈ ls := by
            rcases List.mem_append.mp hk with h1 | h2
            · exact h1
            · exact False.elim (hkj (List.mem_singleton.mp h2))
          exact hprev.2.2.2.2 x hx g hg k hkls a
  have h := haux (List.finRange t) (List.nodup_finRange t)
  refine ⟨h.1, h.2.1, by simpa [cMobiusAll, foldFin] using h.2.2.1,
    by simpa [cMobiusAll, foldFin] using h.2.2.2.1,
    fun x hx g hg j a => h.2.2.2.2 x hx g hg j (List.mem_finRange j) a⟩

private def cShiftCoord {n d : ℕ} (inputs : ℕ)
    (enumerate : Fin (lowSet n d).card ≃ ↥(lowSet n d))
    (r : Fin n) (vBit : ℕ) (st : List Gate × (Fin (lowSet n d).card → ℕ)) :
    List Gate × (Fin (lowSet n d).card → ℕ) :=
  let oldArr := st.2
  foldFin (lowSet n d).card (fun a cur =>
    let S := (enumerate a).val
    if h : r ∉ S ∧ insert r S ∈ lowSet n d then
      let a' := enumerate.symm ⟨insert r S, h.2⟩
      let (gs1, wProd) := mkAnd inputs cur.1 vBit (oldArr a')
      let (gs2, wNew) := mkXor inputs gs1 (oldArr a) wProd
      (gs2, fun b => if b = a then wNew else cur.2 b)
    else cur) (st.1, oldArr)

private theorem cShiftCoord_spec {n d : ℕ} {inputs : ℕ}
    (enumerate : Fin (lowSet n d).card ≃ ↥(lowSet n d))
    (r : Fin n) (vBit : ℕ) (gs : List Gate) (arr : Fin (lowSet n d).card → ℕ)
    (hV : ValidG inputs gs) (hv : vBit < inputs + gs.length)
    (harr : ∀ a, arr a < inputs + gs.length) :
    let res := cShiftCoord inputs enumerate r vBit (gs, arr)
    ValidG inputs res.1 ∧ Extends gs res.1 ∧
    res.1.length ≤ gs.length + 5 * (lowSet n d).card ∧
    (∀ a, res.2 a < inputs + res.1.length) ∧
    ∀ (x : List Bool) (_hx : x.length = inputs) (b : F) (c : Finset (Fin n) → F),
      evalW gs x vBit = b →
      (∀ a, evalW gs x (arr a) = c (enumerate a).val) →
      ∀ a, evalW res.1 x (res.2 a) = shiftCoord d r b c (enumerate a).val := by
  have haux : ∀ (l : List (Fin (lowSet n d).card)), l.Nodup →
      let res := l.foldl (fun cur a =>
        let S := (enumerate a).val
        if h : r ∉ S ∧ insert r S ∈ lowSet n d then
          let a' := enumerate.symm ⟨insert r S, h.2⟩
          let (gs1, wProd) := mkAnd inputs cur.1 vBit (arr a')
          let (gs2, wNew) := mkXor inputs gs1 (arr a) wProd
          (gs2, fun b => if b = a then wNew else cur.2 b)
        else cur) (gs, arr)
      ValidG inputs res.1 ∧ Extends gs res.1 ∧
      res.1.length ≤ gs.length + 5 * l.length ∧
      (∀ a, res.2 a < inputs + res.1.length) ∧
      ∀ (x : List Bool) (_hx : x.length = inputs) (bv : F) (c : Finset (Fin n) → F),
        evalW gs x vBit = bv →
        (∀ a, evalW gs x (arr a) = c (enumerate a).val) →
        ∀ a, evalW res.1 x (res.2 a) = if a ∈ l then shiftCoord d r bv c (enumerate a).val else c (enumerate a).val := by
    intro l hl
    induction l using List.reverseRecOn with
    | nil =>
      refine ⟨hV, extends_refl gs, by simp, harr, fun x _ bv c _ hc a => by simp [hc a]⟩
    | append_singleton ls a ih =>
      have hls : ls.Nodup := (List.nodup_append.mp hl).1
      have hna : a ∉ ls := by
        intro hmem
        exact (List.nodup_append.mp hl).2.2 a hmem a (List.mem_singleton_self a) rfl
      have hprev := ih hls
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append,
        List.length_cons, List.length_nil]
      set cur := ls.foldl (fun cur a =>
        let S := (enumerate a).val
        if h : r ∉ S ∧ insert r S ∈ lowSet n d then
          let a' := enumerate.symm ⟨insert r S, h.2⟩
          let (gs1, wProd) := mkAnd inputs cur.1 vBit (arr a')
          let (gs2, wNew) := mkXor inputs gs1 (arr a) wProd
          (gs2, fun b => if b = a then wNew else cur.2 b)
        else cur) (gs, arr)
      by_cases hcond : r ∉ (enumerate a).val ∧ insert r (enumerate a).val ∈ lowSet n d
      · rw [dif_pos hcond]
        set a' := enumerate.symm ⟨insert r (enumerate a).val, hcond.2⟩
        have hv_cur : vBit < inputs + cur.1.length := lt_of_lt_of_le hv (Nat.add_le_add_left (extends_len hprev.2.1) _)
        have ha'_cur : arr a' < inputs + cur.1.length := lt_of_lt_of_le (harr a') (Nat.add_le_add_left (extends_len hprev.2.1) _)
        have hand := mkAnd_spec hprev.1 hv_cur ha'_cur
        set gs1 := (mkAnd inputs cur.1 vBit (arr a')).1
        set wProd := (mkAnd inputs cur.1 vBit (arr a')).2
        have ha_1 : arr a < inputs + gs1.length := lt_of_lt_of_le (harr a) (Nat.add_le_add_left (extends_len (extends_trans hprev.2.1 hand.2.1)) _)
        have hxor := mkXor_spec hand.1 ha_1 hand.2.2.2.1
        set gs2 := (mkXor inputs gs1 (arr a) wProd).1
        set wNew := (mkXor inputs gs1 (arr a) wProd).2
        have hext12 : Extends cur.1 gs2 := extends_trans hand.2.1 hxor.2.1
        have hl_prev : cur.1.length ≤ gs.length + 5 * ls.length := hprev.2.2.1
        have hl_and : gs1.length = cur.1.length + 1 := hand.2.2.1
        have hl_xor : gs2.length = gs1.length + 4 := hxor.2.2.1
        refine ⟨hxor.1, extends_trans hprev.2.1 hext12, by change gs2.length ≤ _; omega, ?_, ?_⟩
        · intro b
          by_cases hba : b = a
          · subst hba; simpa using hxor.2.2.2.1
          · simp only [hba, ↓reduceIte]
            exact lt_of_lt_of_le (hprev.2.2.2.1 b) (Nat.add_le_add_left (extends_len hext12) _)
        · intro x hx bv c hbv hc b
          by_cases hba : b = a
          · subst hba
            simp only [↓reduceIte, List.mem_append, List.mem_singleton, or_true]
            rw [hxor.2.2.2.2 x hx, evalW_extends (extends_trans hprev.2.1 hand.2.1) hx (harr b),
              hand.2.2.2.2 x hx, evalW_extends hprev.2.1 hx hv, evalW_extends hprev.2.1 hx (harr a'),
              hbv, hc b, hc a']
            have hS' : (enumerate a').val = insert r (enumerate b).val := by simp [a']
            rw [hS']
            simp [shiftCoord, hcond]
          · simp only [hba, ↓reduceIte, List.mem_append, List.mem_singleton, or_false]
            rw [evalW_extends hext12 hx (hprev.2.2.2.1 b)]
            exact hprev.2.2.2.2 x hx bv c hbv hc b
      · rw [dif_neg hcond]
        have hl_prev := hprev.2.2.1
        refine ⟨hprev.1, hprev.2.1, by omega, hprev.2.2.2.1, ?_⟩
        intro x hx bv c hbv hc b
        by_cases hba : b = a
        · subst hba
          simp only [List.mem_append, List.mem_singleton, or_true, ↓reduceIte]
          rw [hprev.2.2.2.2 x hx bv c hbv hc b, if_neg hna]
          simp [shiftCoord, hcond]
        · simp only [List.mem_append, List.mem_singleton, hba, or_false]
          exact hprev.2.2.2.2 x hx bv c hbv hc b
  have h := haux (List.finRange (lowSet n d).card) (List.nodup_finRange _)
  simpa [cShiftCoord, foldFin, List.mem_finRange] using h

private def cShiftOne {n d : ℕ} (inputs : ℕ)
    (enumerate : Fin (lowSet n d).card ≃ ↥(lowSet n d))
    (gs : List Gate) (vW : Fin n → ℕ) (cW : Fin (lowSet n d).card → ℕ) :
    List Gate × (Fin (lowSet n d).card → ℕ) :=
  foldFin n (fun r cur => cShiftCoord inputs enumerate r (vW r) cur) (gs, cW)

private theorem cShiftOne_spec {n d : ℕ} {inputs : ℕ}
    (enumerate : Fin (lowSet n d).card ≃ ↥(lowSet n d))
    (gs : List Gate) (vW : Fin n → ℕ) (cW : Fin (lowSet n d).card → ℕ)
    (hV : ValidG inputs gs) (hv : ∀ r, vW r < inputs + gs.length)
    (hc : ∀ a, cW a < inputs + gs.length) :
    let res := cShiftOne inputs enumerate gs vW cW
    ValidG inputs res.1 ∧ Extends gs res.1 ∧
    res.1.length ≤ gs.length + 5 * n * (lowSet n d).card ∧
    (∀ a, res.2 a < inputs + res.1.length) ∧
    ∀ (x : List Bool) (_hx : x.length = inputs) (v : Vec n) (c : Finset (Fin n) → F),
      (∀ r, evalW gs x (vW r) = v r) →
      (∀ a, evalW gs x (cW a) = c (enumerate a).val) →
      ∀ a, evalW res.1 x (res.2 a) = shiftVec d v c (enumerate a).val := by
  have haux : ∀ (l : List (Fin n)),
      let res := l.foldl (fun cur r => cShiftCoord inputs enumerate r (vW r) cur) (gs, cW)
      ValidG inputs res.1 ∧ Extends gs res.1 ∧
      res.1.length ≤ gs.length + 5 * l.length * (lowSet n d).card ∧
      (∀ a, res.2 a < inputs + res.1.length) ∧
      ∀ (x : List Bool) (_hx : x.length = inputs) (v : Vec n) (c : Finset (Fin n) → F),
        (∀ r, evalW gs x (vW r) = v r) →
        (∀ a, evalW gs x (cW a) = c (enumerate a).val) →
        ∀ a, evalW res.1 x (res.2 a) = shiftFold d l v c (enumerate a).val := by
    intro l
    induction l using List.reverseRecOn with
    | nil =>
      refine ⟨hV, extends_refl gs, by simp, hc, fun x _ v c _ hce a => by simpa [shiftFold] using hce a⟩
    | append_singleton ls r ih =>
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append,
        List.length_cons, List.length_nil]
      set cur := ls.foldl (fun cur r => cShiftCoord inputs enumerate r (vW r) cur) (gs, cW)
      have hvr : vW r < inputs + cur.1.length := lt_of_lt_of_le (hv r) (Nat.add_le_add_left (extends_len ih.2.1) _)
      have hstep := cShiftCoord_spec enumerate r (vW r) cur.1 cur.2 ih.1 hvr ih.2.2.2.1
      refine ⟨hstep.1, extends_trans ih.2.1 hstep.2.1, ?_, hstep.2.2.2.1, ?_⟩
      · have h1 := ih.2.2.1
        have h2 := hstep.2.2.1
        nlinarith
      · intro x hx v c hve hce a
        have hfold : shiftFold d (ls ++ [r]) v c = shiftCoord d r (v r) (shiftFold d ls v c) := by
          simp [shiftFold, List.foldl_append]
        rw [hfold]
        exact hstep.2.2.2.2 x hx (v r) (shiftFold d ls v c)
          (by rw [evalW_extends ih.2.1 hx (hv r), hve r])
          (ih.2.2.2.2 x hx v c hve hce) a
  have h := haux (List.finRange n)
  simpa [cShiftOne, foldFin, shiftVec] using h

private def cXorArr {m : ℕ} (inputs : ℕ) (gs : List Gate) (aW bW : Fin m → ℕ) :
    List Gate × (Fin m → ℕ) :=
  foldFin m (fun i cur =>
    let (gs', w) := mkXor inputs cur.1 (aW i) (bW i)
    (gs', fun k => if k = i then w else cur.2 k)) (gs, aW)

private theorem cXorArr_spec {m : ℕ} {inputs : ℕ} (gs : List Gate) (aW bW : Fin m → ℕ)
    (hV : ValidG inputs gs) (ha : ∀ i, aW i < inputs + gs.length) (hb : ∀ i, bW i < inputs + gs.length) :
    let res := cXorArr inputs gs aW bW
    ValidG inputs res.1 ∧ Extends gs res.1 ∧
    res.1.length = gs.length + 4 * m ∧
    (∀ i, res.2 i < inputs + res.1.length) ∧
    ∀ (x : List Bool) (_hx : x.length = inputs) (i : Fin m),
      evalW res.1 x (res.2 i) = evalW gs x (aW i) + evalW gs x (bW i) := by
  have haux : ∀ (l : List (Fin m)), l.Nodup →
      let res := l.foldl (fun cur i =>
        let (gs', w) := mkXor inputs cur.1 (aW i) (bW i)
        (gs', fun k => if k = i then w else cur.2 k)) (gs, aW)
      ValidG inputs res.1 ∧ Extends gs res.1 ∧
      res.1.length = gs.length + 4 * l.length ∧
      (∀ i, res.2 i < inputs + res.1.length) ∧
      ∀ (x : List Bool) (_hx : x.length = inputs) (i : Fin m), i ∈ l →
        evalW res.1 x (res.2 i) = evalW gs x (aW i) + evalW gs x (bW i) := by
    intro l hl
    induction l using List.reverseRecOn with
    | nil =>
      refine ⟨hV, extends_refl gs, by simp, ha, fun _ _ _ hi => by cases hi⟩
    | append_singleton ls i ih =>
      have hls : ls.Nodup := (List.nodup_append.mp hl).1
      have hprev := ih hls
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append,
        List.length_cons, List.length_nil]
      set cur := ls.foldl (fun cur i =>
        let (gs', w) := mkXor inputs cur.1 (aW i) (bW i)
        (gs', fun k => if k = i then w else cur.2 k)) (gs, aW)
      have hai : aW i < inputs + cur.1.length := lt_of_lt_of_le (ha i) (Nat.add_le_add_left (extends_len hprev.2.1) _)
      have hbi : bW i < inputs + cur.1.length := lt_of_lt_of_le (hb i) (Nat.add_le_add_left (extends_len hprev.2.1) _)
      have hxor := mkXor_spec hprev.1 hai hbi
      refine ⟨hxor.1, extends_trans hprev.2.1 hxor.2.1, by omega, ?_, ?_⟩
      · intro k
        by_cases hki : k = i
        · subst hki; simpa using hxor.2.2.2.1
        · simp only [hki, ↓reduceIte]
          exact lt_of_lt_of_le (hprev.2.2.2.1 k) (Nat.add_le_add_left (extends_len hxor.2.1) _)
      · intro x hx k hk
        by_cases hki : k = i
        · subst hki
          simp only [↓reduceIte]
          rw [hxor.2.2.2.2 x hx, evalW_extends hprev.2.1 hx (ha k), evalW_extends hprev.2.1 hx (hb k)]
        · simp only [hki, ↓reduceIte]
          rw [evalW_extends hxor.2.1 hx (hprev.2.2.2.1 k)]
          have hkls : k ∈ ls := by
            rcases List.mem_append.mp hk with h1 | h2
            · exact h1
            · exact False.elim (hki (List.mem_singleton.mp h2))
          exact hprev.2.2.2.2 x hx k hkls
  have h := haux (List.finRange m) (List.nodup_finRange m)
  refine ⟨h.1, h.2.1, by simpa [cXorArr, foldFin] using h.2.2.1,
    by simpa [cXorArr, foldFin] using h.2.2.2.1,
    fun x hx i => h.2.2.2.2 x hx i (List.mem_finRange i)⟩

private def cDeltaAll {n t d : ℕ} (inputs : ℕ)
    (enumerate : Fin (lowSet n d).card ≃ ↥(lowSet n d))
    (gs : List Gate) (cW : Fin t → Fin (lowSet n d).card → ℕ) (vW : Fin n → ℕ) :
    List Gate × (Fin t → Fin (lowSet n d).card → ℕ) :=
  foldFin t (fun j cur =>
    let (gs1, sW) := cShiftOne inputs enumerate cur.1 vW (cW j)
    let (gs2, dW) := cXorArr inputs gs1 sW (cW j)
    (gs2, fun k => if k = j then dW else cur.2 k)) (gs, cW)

private theorem cDeltaAll_spec {n t d : ℕ} {inputs : ℕ}
    (enumerate : Fin (lowSet n d).card ≃ ↥(lowSet n d))
    (gs : List Gate) (cW : Fin t → Fin (lowSet n d).card → ℕ) (vW : Fin n → ℕ)
    (hV : ValidG inputs gs) (hc : ∀ j a, cW j a < inputs + gs.length) (hv : ∀ r, vW r < inputs + gs.length) :
    let res := cDeltaAll inputs enumerate gs cW vW
    ValidG inputs res.1 ∧ Extends gs res.1 ∧
    res.1.length ≤ gs.length + t * (5 * n + 4) * (lowSet n d).card ∧
    (∀ j a, res.2 j a < inputs + res.1.length) ∧
    ∀ (x : List Bool) (_hx : x.length = inputs) (c : Fin t → Finset (Fin n) → F) (v : Vec n),
      (∀ j a, evalW gs x (cW j a) = c j (enumerate a).val) →
      (∀ r, evalW gs x (vW r) = v r) →
      ∀ j a, evalW res.1 x (res.2 j a) = delta d c v j (enumerate a).val := by
  have haux : ∀ (l : List (Fin t)), l.Nodup →
      let res := l.foldl (fun cur j =>
        let (gs1, sW) := cShiftOne inputs enumerate cur.1 vW (cW j)
        let (gs2, dW) := cXorArr inputs gs1 sW (cW j)
        (gs2, fun k => if k = j then dW else cur.2 k)) (gs, cW)
      ValidG inputs res.1 ∧ Extends gs res.1 ∧
      res.1.length ≤ gs.length + l.length * (5 * n + 4) * (lowSet n d).card ∧
      (∀ j a, res.2 j a < inputs + res.1.length) ∧
      ∀ (x : List Bool) (_hx : x.length = inputs) (c : Fin t → Finset (Fin n) → F) (v : Vec n),
        (∀ j a, evalW gs x (cW j a) = c j (enumerate a).val) →
        (∀ r, evalW gs x (vW r) = v r) →
        ∀ j ∈ l, ∀ a, evalW res.1 x (res.2 j a) = delta d c v j (enumerate a).val := by
    intro l hl
    induction l using List.reverseRecOn with
    | nil =>
      refine ⟨hV, extends_refl gs, by simp, hc, fun _ _ _ _ _ _ _ hj => by cases hj⟩
    | append_singleton ls j ih =>
      have hls : ls.Nodup := (List.nodup_append.mp hl).1
      have hprev := ih hls
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append,
        List.length_cons, List.length_nil]
      set cur := ls.foldl (fun cur j =>
        let (gs1, sW) := cShiftOne inputs enumerate cur.1 vW (cW j)
        let (gs2, dW) := cXorArr inputs gs1 sW (cW j)
        (gs2, fun k => if k = j then dW else cur.2 k)) (gs, cW)
      have hv_c : ∀ r, vW r < inputs + cur.1.length :=
        fun r => lt_of_lt_of_le (hv r) (Nat.add_le_add_left (extends_len hprev.2.1) _)
      have hc_c : ∀ a, cW j a < inputs + cur.1.length :=
        fun a => lt_of_lt_of_le (hc j a) (Nat.add_le_add_left (extends_len hprev.2.1) _)
      have hsh := cShiftOne_spec enumerate cur.1 vW (cW j) hprev.1 hv_c hc_c
      set gs1 := (cShiftOne inputs enumerate cur.1 vW (cW j)).1
      set sW := (cShiftOne inputs enumerate cur.1 vW (cW j)).2
      have hc_1 : ∀ a, cW j a < inputs + gs1.length :=
        fun a => lt_of_lt_of_le (hc_c a) (Nat.add_le_add_left (extends_len hsh.2.1) _)
      have hxo := cXorArr_spec gs1 sW (cW j) hsh.1 hsh.2.2.2.1 hc_1
      set gs2 := (cXorArr inputs gs1 sW (cW j)).1
      set dW := (cXorArr inputs gs1 sW (cW j)).2
      have hext12 : Extends cur.1 gs2 := extends_trans hsh.2.1 hxo.2.1
      refine ⟨hxo.1, extends_trans hprev.2.1 hext12, ?_, ?_, ?_⟩
      · have h1 := hprev.2.2.1
        have h2 := hsh.2.2.1
        have h3 := hxo.2.2.1
        nlinarith
      · intro k a
        by_cases hkj : k = j
        · subst hkj; simpa using hxo.2.2.2.1 a
        · simp only [hkj, ↓reduceIte]
          exact lt_of_lt_of_le (hprev.2.2.2.1 k a) (Nat.add_le_add_left (extends_len hext12) _)
      · intro x hx c v hce hve k hk a
        by_cases hkj : k = j
        · subst hkj
          simp only [↓reduceIte]
          rw [hxo.2.2.2.2 x hx a,
            hsh.2.2.2.2 x hx v (c k)
              (fun r => by rw [evalW_extends hprev.2.1 hx (hv r), hve r])
              (fun b => by rw [evalW_extends hprev.2.1 hx (hc k b), hce k b]) a,
            evalW_extends (extends_trans hprev.2.1 hsh.2.1) hx (hc k a), hce k a]
          rfl
        · simp only [hkj, ↓reduceIte]
          rw [evalW_extends hext12 hx (hprev.2.2.2.1 k a)]
          have hkls : k ∈ ls := by
            rcases List.mem_append.mp hk with h1 | h2
            · exact h1
            · exact False.elim (hkj (List.mem_singleton.mp h2))
          exact hprev.2.2.2.2 x hx c v hce hve k hkls a
  have h := haux (List.finRange t) (List.nodup_finRange t)
  refine ⟨h.1, h.2.1, by simpa [cDeltaAll, foldFin] using h.2.2.1,
    by simpa [cDeltaAll, foldFin] using h.2.2.2.1,
    fun x hx c v hce hve j a => h.2.2.2.2 x hx c v hce hve j (List.mem_finRange j) a⟩

private def cEStep {n : ℕ} (inputs : ℕ) (p : Fin n)
    (st : List Gate × (Fin n → Fin n → ℕ) × (Fin n → ℕ)) :
    List Gate × (Fin n → Fin n → ℕ) × (Fin n → ℕ) :=
  let gs0 := st.1
  let EW := st.2.1
  let wW := st.2.2
  let hit := wW p
  let (gs1, empty) := mkNot inputs gs0 (EW p p)
  let (gs2, place) := mkAnd inputs gs1 hit empty
  let (gs3, notPlace) := mkNot inputs gs2 place
  foldFin n (fun q cur =>
    let (g1, pw) := mkAnd inputs cur.1 place (wW q)
    let (g2, newE) := mkXor inputs g1 (EW p q) pw
    let (g3, hE) := mkAnd inputs g2 hit (EW p q)
    let (g4, xw) := mkXor inputs g3 (wW q) hE
    let (g5, newW) := mkAnd inputs g4 notPlace xw
    (g5,
      fun i j => if i = p ∧ j = q then newE else cur.2.1 i j,
      fun j => if j = q then newW else cur.2.2 j)) (gs3, EW, wW)

private theorem cEStep_spec {n : ℕ} {inputs : ℕ} (p : Fin n)
    (gs : List Gate) (EW : Fin n → Fin n → ℕ) (wW : Fin n → ℕ)
    (hV : ValidG inputs gs)
    (hEW : ∀ i j, EW i j < inputs + gs.length) (hwW : ∀ j, wW j < inputs + gs.length) :
    let res := cEStep inputs p (gs, EW, wW)
    ValidG inputs res.1 ∧ Extends gs res.1 ∧
    res.1.length = gs.length + 3 + 11 * n ∧
    (∀ i j, res.2.1 i j < inputs + res.1.length) ∧
    (∀ j, res.2.2 j < inputs + res.1.length) ∧
    ∀ (x : List Bool) (_hx : x.length = inputs) (E : Mat n) (w : Vec n),
      (∀ i j, evalW gs x (EW i j) = E i j) →
      (∀ j, evalW gs x (wW j) = w j) →
      (∀ i j, evalW res.1 x (res.2.1 i j) = (eStep p (E, w)).1 i j) ∧
      (∀ j, evalW res.1 x (res.2.2 j) = (eStep p (E, w)).2 j) := by
  unfold cEStep
  have h1 := mkNot_spec hV (hEW p p)
  set gs1 := (mkNot inputs gs (EW p p)).1
  set empty := (mkNot inputs gs (EW p p)).2
  have hhit1 : wW p < inputs + gs1.length := lt_of_lt_of_le (hwW p) (Nat.add_le_add_left (extends_len h1.2.1) _)
  have h2 := mkAnd_spec h1.1 hhit1 h1.2.2.2.1
  set gs2 := (mkAnd inputs gs1 (wW p) empty).1
  set place := (mkAnd inputs gs1 (wW p) empty).2
  have h3 := mkNot_spec h2.1 h2.2.2.2.1
  set gs3 := (mkNot inputs gs2 place).1
  set notPlace := (mkNot inputs gs2 place).2
  have hext03 : Extends gs gs3 := extends_trans (extends_trans h1.2.1 h2.2.1) h3.2.1
  have hl1 : gs1.length = gs.length + 1 := h1.2.2.1
  have hl2 : gs2.length = gs1.length + 1 := h2.2.2.1
  have hl3 : gs3.length = gs2.length + 1 := h3.2.2.1
  have hlen3 : gs3.length = gs.length + 3 := by omega
  have hplace3 : place < inputs + gs3.length := lt_of_lt_of_le h2.2.2.2.1 (Nat.add_le_add_left (extends_len h3.2.1) _)
  have hhit3 : wW p < inputs + gs3.length := lt_of_lt_of_le (hwW p) (Nat.add_le_add_left (extends_len hext03) _)
  have hEW3 : ∀ i j, EW i j < inputs + gs3.length := fun i j => lt_of_lt_of_le (hEW i j) (Nat.add_le_add_left (extends_len hext03) _)
  have hwW3 : ∀ j, wW j < inputs + gs3.length := fun j => lt_of_lt_of_le (hwW j) (Nat.add_le_add_left (extends_len hext03) _)
  have haux : ∀ (l : List (Fin n)), l.Nodup →
      let res := l.foldl (fun cur q =>
        let (g1, pw) := mkAnd inputs cur.1 place (wW q)
        let (g2, newE) := mkXor inputs g1 (EW p q) pw
        let (g3, hE) := mkAnd inputs g2 (wW p) (EW p q)
        let (g4, xw) := mkXor inputs g3 (wW q) hE
        let (g5, newW) := mkAnd inputs g4 notPlace xw
        (g5,
          fun i j => if i = p ∧ j = q then newE else cur.2.1 i j,
          fun j => if j = q then newW else cur.2.2 j)) (gs3, EW, wW)
      ValidG inputs res.1 ∧ Extends gs3 res.1 ∧
      res.1.length = gs3.length + 11 * l.length ∧
      (∀ i j, res.2.1 i j < inputs + res.1.length) ∧
      (∀ j, res.2.2 j < inputs + res.1.length) ∧
      ∀ (x : List Bool) (_hx : x.length = inputs) (E : Mat n) (w : Vec n),
        (∀ i j, evalW gs x (EW i j) = E i j) →
        (∀ j, evalW gs x (wW j) = w j) →
        (∀ i j, evalW res.1 x (res.2.1 i j) = if i = p ∧ j ∈ l then (eStep p (E, w)).1 i j else E i j) ∧
        (∀ j, evalW res.1 x (res.2.2 j) = if j ∈ l then (eStep p (E, w)).2 j else w j) := by
    intro l hl
    induction l using List.reverseRecOn with
    | nil =>
      refine ⟨h3.1, extends_refl gs3, by simp, hEW3, hwW3, fun x hx E w hEe hwe => ⟨?_, ?_⟩⟩
      · intro i j; simp only [List.foldl_nil, List.not_mem_nil, and_false, ↓reduceIte]
        rw [evalW_extends hext03 hx (hEW i j), hEe i j]
      · intro j; simp only [List.foldl_nil, List.not_mem_nil, ↓reduceIte]
        rw [evalW_extends hext03 hx (hwW j), hwe j]
    | append_singleton ls q ih =>
      have hls : ls.Nodup := (List.nodup_append.mp hl).1
      have hprev := ih hls
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append,
        List.length_cons, List.length_nil]
      set cur := ls.foldl (fun cur q =>
        let (g1, pw) := mkAnd inputs cur.1 place (wW q)
        let (g2, newE) := mkXor inputs g1 (EW p q) pw
        let (g3, hE) := mkAnd inputs g2 (wW p) (EW p q)
        let (g4, xw) := mkXor inputs g3 (wW q) hE
        let (g5, newW) := mkAnd inputs g4 notPlace xw
        (g5,
          fun i j => if i = p ∧ j = q then newE else cur.2.1 i j,
          fun j => if j = q then newW else cur.2.2 j)) (gs3, EW, wW)
      have hext0c : Extends gs cur.1 := extends_trans hext03 hprev.2.1
      have hp_c : place < inputs + cur.1.length := lt_of_lt_of_le hplace3 (Nat.add_le_add_left (extends_len hprev.2.1) _)
      have hnp_c : notPlace < inputs + cur.1.length := lt_of_lt_of_le h3.2.2.2.1 (Nat.add_le_add_left (extends_len hprev.2.1) _)
      have hwq_c : wW q < inputs + cur.1.length := lt_of_lt_of_le (hwW q) (Nat.add_le_add_left (extends_len hext0c) _)
      have hEpq_c : EW p q < inputs + cur.1.length := lt_of_lt_of_le (hEW p q) (Nat.add_le_add_left (extends_len hext0c) _)
      have hhit_c : wW p < inputs + cur.1.length := lt_of_lt_of_le (hwW p) (Nat.add_le_add_left (extends_len hext0c) _)
      have hg1 := mkAnd_spec hprev.1 hp_c hwq_c
      set g1 := (mkAnd inputs cur.1 place (wW q)).1
      set pw := (mkAnd inputs cur.1 place (wW q)).2
      have hEpq_1 : EW p q < inputs + g1.length := lt_of_lt_of_le hEpq_c (Nat.add_le_add_left (extends_len hg1.2.1) _)
      have hg2 := mkXor_spec hg1.1 hEpq_1 hg1.2.2.2.1
      set g2 := (mkXor inputs g1 (EW p q) pw).1
      set newE := (mkXor inputs g1 (EW p q) pw).2
      have hextc2 : Extends cur.1 g2 := extends_trans hg1.2.1 hg2.2.1
      have hhit_2 : wW p < inputs + g2.length := lt_of_lt_of_le hhit_c (Nat.add_le_add_left (extends_len hextc2) _)
      have hEpq_2 : EW p q < inputs + g2.length := lt_of_lt_of_le hEpq_c (Nat.add_le_add_left (extends_len hextc2) _)
      have hg3 := mkAnd_spec hg2.1 hhit_2 hEpq_2
      set g3 := (mkAnd inputs g2 (wW p) (EW p q)).1
      set hE := (mkAnd inputs g2 (wW p) (EW p q)).2
      have hextc3 : Extends cur.1 g3 := extends_trans hextc2 hg3.2.1
      have hwq_3 : wW q < inputs + g3.length := lt_of_lt_of_le hwq_c (Nat.add_le_add_left (extends_len hextc3) _)
      have hg4 := mkXor_spec hg3.1 hwq_3 hg3.2.2.2.1
      set g4 := (mkXor inputs g3 (wW q) hE).1
      set xw := (mkXor inputs g3 (wW q) hE).2
      have hextc4 : Extends cur.1 g4 := extends_trans hextc3 hg4.2.1
      have hnp_4 : notPlace < inputs + g4.length := lt_of_lt_of_le hnp_c (Nat.add_le_add_left (extends_len hextc4) _)
      have hg5 := mkAnd_spec hg4.1 hnp_4 hg4.2.2.2.1
      set g5 := (mkAnd inputs g4 notPlace xw).1
      set newW := (mkAnd inputs g4 notPlace xw).2
      have hextc5 : Extends cur.1 g5 := extends_trans hextc4 hg5.2.1
      have hext25 : Extends g2 g5 := extends_trans (extends_trans hg3.2.1 hg4.2.1) hg5.2.1
      have hlp : cur.1.length = gs3.length + 11 * ls.length := hprev.2.2.1
      have hlg1 : g1.length = cur.1.length + 1 := hg1.2.2.1
      have hlg2 : g2.length = g1.length + 4 := hg2.2.2.1
      have hlg3 : g3.length = g2.length + 1 := hg3.2.2.1
      have hlg4 : g4.length = g3.length + 4 := hg4.2.2.1
      have hlg5 : g5.length = g4.length + 1 := hg5.2.2.1
      refine ⟨hg5.1, extends_trans hprev.2.1 hextc5, by change g5.length = _; omega, ?_, ?_, ?_⟩
      · intro i j
        by_cases hij : i = p ∧ j = q
        · simp only [hij, and_self, ↓reduceIte]
          exact lt_of_lt_of_le hg2.2.2.2.1 (Nat.add_le_add_left (extends_len hext25) _)
        · simp only [hij, ↓reduceIte]
          exact lt_of_lt_of_le (hprev.2.2.2.1 i j) (Nat.add_le_add_left (extends_len hextc5) _)
      · intro j
        by_cases hjq : j = q
        · subst hjq; simpa using hg5.2.2.2.1
        · simp only [hjq, ↓reduceIte]
          exact lt_of_lt_of_le (hprev.2.2.2.2.1 j) (Nat.add_le_add_left (extends_len hextc5) _)
      · intro x hx E w hEe hwe
        have hv_place : evalW cur.1 x place = w p * (1 + E p p) := by
          rw [evalW_extends hprev.2.1 hx hplace3, evalW_extends h3.2.1 hx h2.2.2.2.1,
            h2.2.2.2.2 x hx, evalW_extends h1.2.1 hx (hwW p), h1.2.2.2.2 x hx, hwe p, hEe p p]
        have hv_nplace : evalW g4 x notPlace = 1 + w p * (1 + E p p) := by
          rw [evalW_extends hextc4 hx hnp_c, evalW_extends hprev.2.1 hx h3.2.2.2.1,
            h3.2.2.2.2 x hx, h2.2.2.2.2 x hx, evalW_extends h1.2.1 hx (hwW p),
            h1.2.2.2.2 x hx, hwe p, hEe p p]
        have hv_newE : evalW g5 x newE = E p q + w p * (1 + E p p) * w q := by
          rw [evalW_extends hext25 hx hg2.2.2.2.1, hg2.2.2.2.2 x hx,
            evalW_extends (extends_trans hext0c hg1.2.1) hx (hEW p q),
            hg1.2.2.2.2 x hx, hv_place, evalW_extends hext0c hx (hwW q), hEe p q, hwe q]
        have hv_newW : evalW g5 x newW = (1 + w p * (1 + E p p)) * (w q + w p * E p q) := by
          rw [hg5.2.2.2.2 x hx, hv_nplace, hg4.2.2.2.2 x hx,
            evalW_extends (extends_trans hext0c hextc3) hx (hwW q),
            hg3.2.2.2.2 x hx, evalW_extends (extends_trans hext0c hextc2) hx (hwW p),
            evalW_extends (extends_trans hext0c hextc2) hx (hEW p q), hwe q, hwe p, hEe p q]
        constructor
        · intro i j
          by_cases hij : i = p ∧ j = q
          · rcases hij with ⟨rfl, rfl⟩
            simp only [and_self, ↓reduceIte, List.mem_append, List.mem_singleton, or_true]
            rw [hv_newE]; simp [eStep]
          · simp only [hij, ↓reduceIte]
            rw [evalW_extends hextc5 hx (hprev.2.2.2.1 i j),
              (hprev.2.2.2.2.2 x hx E w hEe hwe).1 i j]
            by_cases hip : i = p
            · subst hip
              have hjne : j ≠ q := fun h => hij ⟨rfl, h⟩
              simp [hjne]
            · simp [hip]
        · intro j
          by_cases hjq : j = q
          · subst hjq
            simp only [↓reduceIte, List.mem_append, List.mem_singleton, or_true]
            rw [hv_newW]; rfl
          · simp only [hjq, ↓reduceIte, List.mem_append, List.mem_singleton, or_false]
            rw [evalW_extends hextc5 hx (hprev.2.2.2.2.1 j),
              (hprev.2.2.2.2.2 x hx E w hEe hwe).2 j]
  have h := haux (List.finRange n) (List.nodup_finRange n)
  dsimp only [foldFin]
  refine ⟨h.1, extends_trans hext03 h.2.1, ?_, h.2.2.2.1, h.2.2.2.2.1, fun x hx E w hEe hwe => ?_⟩
  · have hlen := h.2.2.1; rw [List.length_finRange] at hlen; rw [hlen, hlen3]
  · have he := h.2.2.2.2.2 x hx E w hEe hwe
    refine ⟨fun i j => ?_, fun j => ?_⟩
    · have h1 := he.1 i j
      simp only [List.mem_finRange, and_true] at h1
      rw [h1]
      by_cases hip : i = p
      · simp [hip]
      · simp [hip, eStep]
    · simpa [List.mem_finRange] using he.2 j

private def cInsertRowFold {n : ℕ} (inputs : ℕ) (k : ℕ) (hk : k ≤ n)
    (st : List Gate × (Fin n → Fin n → ℕ) × (Fin n → ℕ)) :
    List Gate × (Fin n → Fin n → ℕ) × (Fin n → ℕ) :=
  match k with
  | 0 => st
  | k' + 1 => cEStep inputs ⟨k', by omega⟩ (cInsertRowFold inputs k' (by omega) st)

private def cInsertRow {n : ℕ} (inputs : ℕ)
    (gs : List Gate) (EW : Fin n → Fin n → ℕ) (wW : Fin n → ℕ) :
    List Gate × (Fin n → Fin n → ℕ) :=
  let res := cInsertRowFold inputs n le_rfl (gs, EW, wW)
  (res.1, res.2.1)

private theorem cInsertRowFold_spec {n : ℕ} {inputs : ℕ} (k : ℕ) (hk : k ≤ n)
    (gs : List Gate) (EW : Fin n → Fin n → ℕ) (wW : Fin n → ℕ)
    (hV : ValidG inputs gs)
    (hEW : ∀ i j, EW i j < inputs + gs.length) (hwW : ∀ j, wW j < inputs + gs.length) :
    let res := cInsertRowFold inputs k hk (gs, EW, wW)
    ValidG inputs res.1 ∧ Extends gs res.1 ∧
    res.1.length = gs.length + k * (3 + 11 * n) ∧
    (∀ i j, res.2.1 i j < inputs + res.1.length) ∧
    (∀ j, res.2.2 j < inputs + res.1.length) ∧
    ∀ (x : List Bool) (_hx : x.length = inputs) (E : Mat n) (w : Vec n),
      (∀ i j, evalW gs x (EW i j) = E i j) →
      (∀ j, evalW gs x (wW j) = w j) →
      (∀ i j, evalW res.1 x (res.2.1 i j) = (insertRowFold k hk (E, w)).1 i j) ∧
      (∀ j, evalW res.1 x (res.2.2 j) = (insertRowFold k hk (E, w)).2 j) := by
  induction k with
  | zero =>
    exact ⟨hV, extends_refl gs, by simp [cInsertRowFold], hEW, hwW, fun x _ E w hEe hwe => ⟨hEe, hwe⟩⟩
  | succ k' ih =>
    have hprev := ih (by omega)
    set cur := cInsertRowFold inputs k' (by omega) (gs, EW, wW)
    have hstep := cEStep_spec ⟨k', by omega⟩ cur.1 cur.2.1 cur.2.2 hprev.1 hprev.2.2.2.1 hprev.2.2.2.2.1
    dsimp only [cInsertRowFold]
    refine ⟨hstep.1, extends_trans hprev.2.1 hstep.2.1, ?_, hstep.2.2.2.1, hstep.2.2.2.2.1, ?_⟩
    · have h1 := hprev.2.2.1
      have h2 := hstep.2.2.1
      nlinarith
    · intro x hx E w hEe hwe
      have hp := hprev.2.2.2.2.2 x hx E w hEe hwe
      exact hstep.2.2.2.2.2 x hx _ _ hp.1 hp.2

private def cInsertRows {n : ℕ} (inputs : ℕ) (gs : List Gate) (rowsW : List (Fin n → ℕ)) :
    List Gate × (Fin n → Fin n → ℕ) :=
  rowsW.foldl (fun cur wW => cInsertRow inputs cur.1 cur.2 wW) (gs, fun _ _ => 0)

private theorem forall2_append' {α β : Type*} {R : α → β → Prop}
    {l1 l2 : List α} {r1 r2 : List β}
    (h1 : List.Forall₂ R l1 r1) (h2 : List.Forall₂ R l2 r2) :
    List.Forall₂ R (l1 ++ l2) (r1 ++ r2) := by
  induction h1 with
  | nil => exact h2
  | cons ha _ ih => exact List.Forall₂.cons ha ih

private theorem forall2_append_singleton_left {α β : Type*} {R : α → β → Prop}
    {rs : List α} {w : α} {rows : List β}
    (h : List.Forall₂ R (rs ++ [w]) rows) :
    ∃ rs' r', List.Forall₂ R rs rs' ∧ R w r' ∧ rows = rs' ++ [r'] := by
  induction rs generalizing rows with
  | nil =>
    cases h with
    | cons hr hnil =>
      cases hnil
      exact ⟨[], _, List.Forall₂.nil, hr, rfl⟩
  | cons a as ih =>
    cases h with
    | cons ha hrest =>
      obtain ⟨rs', r', h1, h2, rfl⟩ := ih hrest
      exact ⟨_ :: rs', r', List.Forall₂.cons ha h1, h2, rfl⟩

private theorem cInsertRows_spec {n : ℕ} {inputs : ℕ} (h0 : 0 < inputs)
    (gs : List Gate) (rowsW : List (Fin n → ℕ))
    (hV : ValidG inputs gs) (hrows : ∀ wW ∈ rowsW, ∀ j, wW j < inputs + gs.length) :
    let res := cInsertRows inputs gs rowsW
    ValidG inputs res.1 ∧ Extends gs res.1 ∧
    res.1.length = gs.length + rowsW.length * (n * (3 + 11 * n)) ∧
    (∀ i j, res.2 i j < inputs + res.1.length) ∧
    ∀ (x : List Bool) (_hx : x.length = inputs) (_hx0 : x.getD 0 false = false)
      (rows : List (Vec n)),
      List.Forall₂ (fun wW r => ∀ j, evalW gs x (wW j) = r j) rowsW rows →
      ∀ i j, evalW res.1 x (res.2 i j) = insertRows rows i j := by
  induction rowsW using List.reverseRecOn with
  | nil =>
    dsimp only [cInsertRows, List.foldl_nil]
    refine ⟨hV, extends_refl gs, by simp, fun _ _ => by omega, ?_⟩
    intro x hx hx0 rows hrel i j
    cases hrel
    simp only [cInsertRows, insertRows, List.foldl_nil]
    have hzero : evalW gs x 0 = 0 := by
      unfold evalW
      obtain ⟨ex, hex⟩ := wiresG_prefix gs x
      rw [hex, getD_append_left' x ex false (by omega), hx0]
      rfl
    exact hzero
  | append_singleton rs wW ih =>
    have hrs : ∀ w ∈ rs, ∀ j, w j < inputs + gs.length :=
      fun w hw => hrows w (List.mem_append_left _ hw)
    have hprev := ih hrs
    simp only [cInsertRows, List.foldl_append, List.foldl_cons, List.foldl_nil,
      List.length_append, List.length_cons, List.length_nil]
    change let res := cInsertRow inputs (cInsertRows inputs gs rs).1 (cInsertRows inputs gs rs).2 wW; _
    set cur := cInsertRows inputs gs rs
    have hwW_c : ∀ j, wW j < inputs + cur.1.length :=
      fun j => lt_of_lt_of_le (hrows wW (List.mem_append_right _ (List.mem_singleton_self _)) j)
        (Nat.add_le_add_left (extends_len hprev.2.1) _)
    have hstep := cInsertRowFold_spec n le_rfl cur.1 cur.2 wW hprev.1 hprev.2.2.2.1 hwW_c
    dsimp only [cInsertRow]
    refine ⟨hstep.1, extends_trans hprev.2.1 hstep.2.1, ?_, hstep.2.2.2.1, ?_⟩
    · have h1 : cur.1.length = gs.length + rs.length * (n * (3 + 11 * n)) := hprev.2.2.1
      have h2 : (cInsertRowFold inputs n le_rfl (cur.1, cur.2, wW)).1.length = cur.1.length + n * (3 + 11 * n) := hstep.2.2.1
      change (cInsertRowFold inputs n le_rfl (cur.1, cur.2, wW)).1.length = _
      nlinarith
    · intro x hx hx0 rows hrel i j
      obtain ⟨rs', r', hrel1, hrel2, rfl⟩ := forall2_append_singleton_left hrel
      have hfold : insertRows (rs' ++ [r']) = insertRow (insertRows rs') r' := by
        simp [insertRows, List.foldl_append]
      rw [hfold]
      exact (hstep.2.2.2.2.2 x hx (insertRows rs') r'
        (hprev.2.2.2.2 x hx hx0 rs' hrel1)
        (fun k => by
          change evalW cur.1 x (wW k) = r' k
          rw [evalW_extends hprev.2.1 hx (hrows wW (List.mem_append_right _ (List.mem_singleton_self _)) k)]
          exact hrel2 k)).1 i j

private def cBackStep {n : ℕ} (inputs : ℕ) (p : Fin n)
    (st : List Gate × (Fin n → Fin n → ℕ)) : List Gate × (Fin n → Fin n → ℕ) :=
  let RW := st.2
  foldFin n (fun i cur =>
    if i.val < p.val then
      foldFin n (fun q cur2 =>
        let (g1, prod) := mkAnd inputs cur2.1 (RW i p) (RW p q)
        let (g2, sum) := mkXor inputs g1 (RW i q) prod
        (g2, fun r c => if r = i ∧ c = q then sum else cur2.2 r c)) cur
    else cur) (st.1, RW)

private theorem cBackStep_spec {n : ℕ} {inputs : ℕ} (p : Fin n)
    (gs : List Gate) (RW : Fin n → Fin n → ℕ)
    (hV : ValidG inputs gs) (hRW : ∀ i j, RW i j < inputs + gs.length) :
    let res := cBackStep inputs p (gs, RW)
    ValidG inputs res.1 ∧ Extends gs res.1 ∧
    res.1.length ≤ gs.length + 5 * n * n ∧
    (∀ i j, res.2 i j < inputs + res.1.length) ∧
    ∀ (x : List Bool) (_hx : x.length = inputs) (R : Mat n),
      (∀ i j, evalW gs x (RW i j) = R i j) →
      ∀ i j, evalW res.1 x (res.2 i j) = backStep p R i j := by
  have hinner : ∀ (i : Fin n) (gs0 : List Gate) (M0 : Fin n → Fin n → ℕ),
      ValidG inputs gs0 → Extends gs gs0 →
      (∀ r c, M0 r c < inputs + gs0.length) →
      let res := foldFin n (fun q cur2 =>
        let (g1, prod) := mkAnd inputs cur2.1 (RW i p) (RW p q)
        let (g2, sum) := mkXor inputs g1 (RW i q) prod
        (g2, fun r c => if r = i ∧ c = q then sum else cur2.2 r c)) (gs0, M0)
      ValidG inputs res.1 ∧ Extends gs0 res.1 ∧
      res.1.length = gs0.length + 5 * n ∧
      (∀ r c, res.2 r c < inputs + res.1.length) ∧
      ∀ (x : List Bool) (_hx : x.length = inputs) (R : Mat n),
        (∀ r c, evalW gs x (RW r c) = R r c) →
        ∀ r c, evalW res.1 x (res.2 r c) =
          if r = i then R i c + R i p * R p c else evalW gs0 x (M0 r c) := by
    intro i gs0 M0 hV0 hext0 hM0
    have hl_aux : ∀ (l : List (Fin n)), l.Nodup →
        let res := l.foldl (fun cur2 q =>
          let (g1, prod) := mkAnd inputs cur2.1 (RW i p) (RW p q)
          let (g2, sum) := mkXor inputs g1 (RW i q) prod
          (g2, fun r c => if r = i ∧ c = q then sum else cur2.2 r c)) (gs0, M0)
        ValidG inputs res.1 ∧ Extends gs0 res.1 ∧
        res.1.length = gs0.length + 5 * l.length ∧
        (∀ r c, res.2 r c < inputs + res.1.length) ∧
        ∀ (x : List Bool) (_hx : x.length = inputs) (R : Mat n),
          (∀ r c, evalW gs x (RW r c) = R r c) →
          ∀ r c, evalW res.1 x (res.2 r c) =
            if r = i ∧ c ∈ l then R i c + R i p * R p c else evalW gs0 x (M0 r c) := by
      intro l hl
      induction l using List.reverseRecOn with
      | nil =>
        refine ⟨hV0, extends_refl gs0, by simp, hM0, fun x _ R _ r c => by simp⟩
      | append_singleton ls q ih =>
        have hls : ls.Nodup := (List.nodup_append.mp hl).1
        have hprev := ih hls
        simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append,
          List.length_cons, List.length_nil]
        set cur2 := ls.foldl (fun cur2 q =>
          let (g1, prod) := mkAnd inputs cur2.1 (RW i p) (RW p q)
          let (g2, sum) := mkXor inputs g1 (RW i q) prod
          (g2, fun r c => if r = i ∧ c = q then sum else cur2.2 r c)) (gs0, M0)
        have hext_gc : Extends gs cur2.1 := extends_trans hext0 hprev.2.1
        have h1w : RW i p < inputs + cur2.1.length := lt_of_lt_of_le (hRW i p) (Nat.add_le_add_left (extends_len hext_gc) _)
        have h2w : RW p q < inputs + cur2.1.length := lt_of_lt_of_le (hRW p q) (Nat.add_le_add_left (extends_len hext_gc) _)
        have hg1 := mkAnd_spec hprev.1 h1w h2w
        set g1 := (mkAnd inputs cur2.1 (RW i p) (RW p q)).1
        set prod := (mkAnd inputs cur2.1 (RW i p) (RW p q)).2
        have h3w : RW i q < inputs + g1.length := lt_of_lt_of_le (hRW i q) (Nat.add_le_add_left (extends_len (extends_trans hext_gc hg1.2.1)) _)
        have hg2 := mkXor_spec hg1.1 h3w hg1.2.2.2.1
        set g2 := (mkXor inputs g1 (RW i q) prod).1
        set sum := (mkXor inputs g1 (RW i q) prod).2
        have hextc2 : Extends cur2.1 g2 := extends_trans hg1.2.1 hg2.2.1
        have hlp : cur2.1.length = gs0.length + 5 * ls.length := hprev.2.2.1
        have hlg1 : g1.length = cur2.1.length + 1 := hg1.2.2.1
        have hlg2 : g2.length = g1.length + 4 := hg2.2.2.1
        refine ⟨hg2.1, extends_trans hprev.2.1 hextc2, by change g2.length = _; omega, ?_, ?_⟩
        · intro r c
          by_cases hrc : r = i ∧ c = q
          · simp only [hrc, and_self, ↓reduceIte]; exact hg2.2.2.2.1
          · simp only [hrc, ↓reduceIte]
            exact lt_of_lt_of_le (hprev.2.2.2.1 r c) (Nat.add_le_add_left (extends_len hextc2) _)
        · intro x hx R hRe r c
          by_cases hrc : r = i ∧ c = q
          · rcases hrc with ⟨rfl, rfl⟩
            simp only [and_self, ↓reduceIte, List.mem_append, List.mem_singleton, or_true]
            rw [hg2.2.2.2.2 x hx, evalW_extends (extends_trans hext_gc hg1.2.1) hx (hRW r c),
              hg1.2.2.2.2 x hx, evalW_extends hext_gc hx (hRW r p),
              evalW_extends hext_gc hx (hRW p c), hRe r c, hRe r p, hRe p c]
          · simp only [hrc, ↓reduceIte]
            rw [evalW_extends hextc2 hx (hprev.2.2.2.1 r c),
              hprev.2.2.2.2 x hx R hRe r c]
            by_cases hri : r = i
            · subst hri
              have hcq : c ≠ q := fun h => hrc ⟨rfl, h⟩
              simp [hcq]
            · simp [hri]
    have h := hl_aux (List.finRange n) (List.nodup_finRange n)
    simpa [foldFin, List.mem_finRange] using h
  have houter : ∀ (l : List (Fin n)), l.Nodup →
      let res := l.foldl (fun cur i =>
        if i.val < p.val then
          foldFin n (fun q cur2 =>
            let (g1, prod) := mkAnd inputs cur2.1 (RW i p) (RW p q)
            let (g2, sum) := mkXor inputs g1 (RW i q) prod
            (g2, fun r c => if r = i ∧ c = q then sum else cur2.2 r c)) cur
        else cur) (gs, RW)
      ValidG inputs res.1 ∧ Extends gs res.1 ∧
      res.1.length ≤ gs.length + 5 * l.length * n ∧
      (∀ r c, res.2 r c < inputs + res.1.length) ∧
      ∀ (x : List Bool) (_hx : x.length = inputs) (R : Mat n),
        (∀ r c, evalW gs x (RW r c) = R r c) →
        ∀ r c, evalW res.1 x (res.2 r c) =
          if r ∈ l ∧ r.val < p.val then R r c + R r p * R p c else R r c := by
    intro l hl
    induction l using List.reverseRecOn with
    | nil =>
      refine ⟨hV, extends_refl gs, by simp, hRW, fun x _ R hRe r c => by simp [hRe r c]⟩
    | append_singleton ls i ih =>
      have hls : ls.Nodup := (List.nodup_append.mp hl).1
      have hni : i ∉ ls := by
        intro hmem
        exact (List.nodup_append.mp hl).2.2 i hmem i (List.mem_singleton_self i) rfl
      have hprev := ih hls
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append,
        List.length_cons, List.length_nil]
      set cur := ls.foldl (fun cur i =>
        if i.val < p.val then
          foldFin n (fun q cur2 =>
            let (g1, prod) := mkAnd inputs cur2.1 (RW i p) (RW p q)
            let (g2, sum) := mkXor inputs g1 (RW i q) prod
            (g2, fun r c => if r = i ∧ c = q then sum else cur2.2 r c)) cur
        else cur) (gs, RW)
      by_cases hlt : i.val < p.val
      · simp only [hlt, ↓reduceIte]
        have hin := hinner i cur.1 cur.2 hprev.1 hprev.2.1 hprev.2.2.2.1
        refine ⟨hin.1, extends_trans hprev.2.1 hin.2.1, ?_, hin.2.2.2.1, ?_⟩
        · have h1 := hprev.2.2.1
          have h2 := hin.2.2.1
          nlinarith
        · intro x hx R hRe r c
          rw [hin.2.2.2.2 x hx R hRe r c]
          by_cases hri : r = i
          · subst hri; simp [hlt]
          · simp only [hri, ↓reduceIte]
            rw [hprev.2.2.2.2 x hx R hRe r c]
            simp [hri]
      · simp only [hlt, ↓reduceIte]
        refine ⟨hprev.1, hprev.2.1, ?_, hprev.2.2.2.1, ?_⟩
        · have h1 := hprev.2.2.1; nlinarith
        · intro x hx R hRe r c
          rw [hprev.2.2.2.2 x hx R hRe r c]
          by_cases hri : r = i
          · subst hri; simp [hni, hlt]
          · simp [hri]
  have h := houter (List.finRange n) (List.nodup_finRange n)
  refine ⟨h.1, h.2.1, by simpa [cBackStep, foldFin] using h.2.2.1,
    by simpa [cBackStep, foldFin] using h.2.2.2.1, fun x hx R hRe r c => ?_⟩
  simpa [cBackStep, foldFin, backStep, List.mem_finRange] using h.2.2.2.2 x hx R hRe r c

private def cBackFold {n : ℕ} (inputs : ℕ) (k : ℕ) (hk : k ≤ n)
    (st : List Gate × (Fin n → Fin n → ℕ)) : List Gate × (Fin n → Fin n → ℕ) :=
  match k with
  | 0 => st
  | k' + 1 => cBackFold inputs k' (by omega) (cBackStep inputs ⟨k', by omega⟩ st)

private theorem cBackFold_spec {n : ℕ} {inputs : ℕ} (k : ℕ) (hk : k ≤ n)
    (gs : List Gate) (RW : Fin n → Fin n → ℕ)
    (hV : ValidG inputs gs) (hRW : ∀ i j, RW i j < inputs + gs.length) :
    let res := cBackFold inputs k hk (gs, RW)
    ValidG inputs res.1 ∧ Extends gs res.1 ∧
    res.1.length ≤ gs.length + 5 * k * n * n ∧
    (∀ i j, res.2 i j < inputs + res.1.length) ∧
    ∀ (x : List Bool) (_hx : x.length = inputs) (R : Mat n),
      (∀ i j, evalW gs x (RW i j) = R i j) →
      ∀ i j, evalW res.1 x (res.2 i j) = backFold k hk R i j := by
  induction k generalizing gs RW with
  | zero =>
    dsimp only [cBackFold]
    exact ⟨hV, extends_refl gs, by simp, hRW, fun x _ R hRe i j => hRe i j⟩
  | succ k' ih =>
    have hstep := cBackStep_spec ⟨k', by omega⟩ gs RW hV hRW
    set st1 := cBackStep inputs ⟨k', by omega⟩ (gs, RW)
    have hrest := ih (by omega) st1.1 st1.2 hstep.1 hstep.2.2.2.1
    dsimp only [cBackFold]
    refine ⟨hrest.1, extends_trans hstep.2.1 hrest.2.1, ?_, hrest.2.2.2.1, ?_⟩
    · have h1 := hstep.2.2.1
      have h2 := hrest.2.2.1
      nlinarith
    · intro x hx R hRe i j
      exact hrest.2.2.2.2 x hx (backStep ⟨k', by omega⟩ R) (hstep.2.2.2.2 x hx R hRe) i j

private def cRREF {n : ℕ} (inputs : ℕ) (gs : List Gate) (rowsW : List (Fin n → ℕ)) :
    List Gate × (Fin n → Fin n → ℕ) :=
  let st := cInsertRows inputs gs rowsW
  cBackFold inputs n le_rfl st

private theorem cRREF_spec {n : ℕ} {inputs : ℕ} (h0 : 0 < inputs)
    (gs : List Gate) (rowsW : List (Fin n → ℕ))
    (hV : ValidG inputs gs) (hrows : ∀ wW ∈ rowsW, ∀ j, wW j < inputs + gs.length) :
    let res := cRREF inputs gs rowsW
    ValidG inputs res.1 ∧ Extends gs res.1 ∧
    res.1.length ≤ gs.length + rowsW.length * (n * (3 + 11 * n)) + 5 * n * n * n ∧
    (∀ i j, res.2 i j < inputs + res.1.length) ∧
    ∀ (x : List Bool) (_hx : x.length = inputs) (_hx0 : x.getD 0 false = false)
      (rows : List (Vec n)),
      List.Forall₂ (fun wW r => ∀ j, evalW gs x (wW j) = r j) rowsW rows →
      ∀ i j, evalW res.1 x (res.2 i j) = rref rows i j := by
  unfold cRREF
  have h1 := cInsertRows_spec h0 gs rowsW hV hrows
  set st := cInsertRows inputs gs rowsW
  have h2 := cBackFold_spec n le_rfl st.1 st.2 h1.1 h1.2.2.2.1
  refine ⟨h2.1, extends_trans h1.2.1 h2.2.1, ?_, h2.2.2.2.1, ?_⟩
  · have ha := h1.2.2.1
    have hb := h2.2.2.1
    nlinarith
  · intro x hx hx0 rows hrel i j
    exact h2.2.2.2.2 x hx (insertRows rows) (h1.2.2.2.2 x hx hx0 rows hrel) i j

private def cKerProj {n : ℕ} (inputs : ℕ) (gs : List Gate) (RW : Fin n → Fin n → ℕ) :
    List Gate × (Fin n → Fin n → ℕ) :=
  foldFin n (fun i cur =>
    let (gs', w) := mkNot inputs cur.1 (RW i i)
    (gs', fun r c => if r = i ∧ c = i then w else cur.2 r c)) (gs, RW)

private theorem cKerProj_spec {n : ℕ} {inputs : ℕ} (gs : List Gate) (RW : Fin n → Fin n → ℕ)
    (hV : ValidG inputs gs) (hRW : ∀ i j, RW i j < inputs + gs.length) :
    let res := cKerProj inputs gs RW
    ValidG inputs res.1 ∧ Extends gs res.1 ∧
    res.1.length = gs.length + n ∧
    (∀ i j, res.2 i j < inputs + res.1.length) ∧
    ∀ (x : List Bool) (_hx : x.length = inputs) (R : Mat n),
      (∀ i j, evalW gs x (RW i j) = R i j) →
      ∀ i j, evalW res.1 x (res.2 i j) = kerProj R i j := by
  have haux : ∀ (l : List (Fin n)), l.Nodup →
      let res := l.foldl (fun cur i =>
        let (gs', w) := mkNot inputs cur.1 (RW i i)
        (gs', fun r c => if r = i ∧ c = i then w else cur.2 r c)) (gs, RW)
      ValidG inputs res.1 ∧ Extends gs res.1 ∧
      res.1.length = gs.length + l.length ∧
      (∀ r c, res.2 r c < inputs + res.1.length) ∧
      ∀ (x : List Bool) (_hx : x.length = inputs) (R : Mat n),
        (∀ r c, evalW gs x (RW r c) = R r c) →
        ∀ r c, evalW res.1 x (res.2 r c) = if r = c ∧ r ∈ l then 1 + R r c else R r c := by
    intro l hl
    induction l using List.reverseRecOn with
    | nil =>
      refine ⟨hV, extends_refl gs, by simp, hRW, fun x _ R hRe r c => by simp [hRe r c]⟩
    | append_singleton ls i ih =>
      have hls : ls.Nodup := (List.nodup_append.mp hl).1
      have hprev := ih hls
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append,
        List.length_cons, List.length_nil]
      set cur := ls.foldl (fun cur i =>
        let (gs', w) := mkNot inputs cur.1 (RW i i)
        (gs', fun r c => if r = i ∧ c = i then w else cur.2 r c)) (gs, RW)
      have hii : RW i i < inputs + cur.1.length := lt_of_lt_of_le (hRW i i) (Nat.add_le_add_left (extends_len hprev.2.1) _)
      have hnot := mkNot_spec hprev.1 hii
      have hlp := hprev.2.2.1; have hln := hnot.2.2.1
      refine ⟨hnot.1, extends_trans hprev.2.1 hnot.2.1, by omega, ?_, ?_⟩
      · intro r c
        by_cases hrc : r = i ∧ c = i
        · simp only [hrc, and_self, ↓reduceIte]; exact hnot.2.2.2.1
        · simp only [hrc, ↓reduceIte]
          exact lt_of_lt_of_le (hprev.2.2.2.1 r c) (Nat.add_le_add_left (extends_len hnot.2.1) _)
      · intro x hx R hRe r c
        by_cases hrc : r = i ∧ c = i
        · rcases hrc with ⟨rfl, rfl⟩
          simp only [and_self, ↓reduceIte, List.mem_append, List.mem_singleton, or_true]
          rw [hnot.2.2.2.2 x hx, evalW_extends hprev.2.1 hx (hRW c c), hRe c c]
        · simp only [hrc, ↓reduceIte]
          rw [evalW_extends hnot.2.1 hx (hprev.2.2.2.1 r c), hprev.2.2.2.2 x hx R hRe r c]
          by_cases hrc' : r = c
          · subst hrc'
            have hri : r ≠ i := fun h => hrc ⟨h, h⟩
            simp [hri]
          · simp [hrc']
  have h := haux (List.finRange n) (List.nodup_finRange n)
  refine ⟨h.1, h.2.1, by simpa [cKerProj, foldFin] using h.2.2.1,
    by simpa [cKerProj, foldFin] using h.2.2.2.1, fun x hx R hRe r c => ?_⟩
  dsimp only [cKerProj, foldFin]
  have he := h.2.2.2.2 x hx R hRe r c
  simp only [List.mem_finRange, and_true] at he
  rw [he]
  unfold kerProj
  split_ifs <;> simp

private def cDot {n : ℕ} (inputs : ℕ) (gs : List Gate) (aW bW : Fin n → ℕ) : List Gate × ℕ :=
  foldFin n (fun k cur =>
    let (g1, p) := mkAnd inputs cur.1 (aW k) (bW k)
    mkXor inputs g1 cur.2 p) (gs, 0)

private theorem cDot_spec {n : ℕ} {inputs : ℕ} (h0 : 0 < inputs) (gs : List Gate)
    (aW bW : Fin n → ℕ) (hV : ValidG inputs gs)
    (ha : ∀ k, aW k < inputs + gs.length) (hb : ∀ k, bW k < inputs + gs.length) :
    let res := cDot inputs gs aW bW
    ValidG inputs res.1 ∧ Extends gs res.1 ∧
    res.1.length = gs.length + 5 * n ∧
    res.2 < inputs + res.1.length ∧
    ∀ (x : List Bool) (_hx : x.length = inputs) (_hx0 : x.getD 0 false = false),
      evalW res.1 x res.2 = ∑ k : Fin n, evalW gs x (aW k) * evalW gs x (bW k) := by
  have haux : ∀ (l : List (Fin n)),
      let res := l.foldl (fun cur k =>
        let (g1, p) := mkAnd inputs cur.1 (aW k) (bW k)
        mkXor inputs g1 cur.2 p) (gs, 0)
      ValidG inputs res.1 ∧ Extends gs res.1 ∧
      res.1.length = gs.length + 5 * l.length ∧
      res.2 < inputs + res.1.length ∧
      ∀ (x : List Bool) (_hx : x.length = inputs) (_hx0 : x.getD 0 false = false),
        evalW res.1 x res.2 = (l.map fun k => evalW gs x (aW k) * evalW gs x (bW k)).sum := by
    intro l
    induction l using List.reverseRecOn with
    | nil =>
      dsimp only [List.foldl_nil]
      refine ⟨hV, extends_refl gs, by simp, by omega, fun x hx hx0 => ?_⟩
      simp only [List.foldl_nil, List.map_nil, List.sum_nil]
      unfold evalW
      obtain ⟨ex, hex⟩ := wiresG_prefix gs x
      rw [hex, getD_append_left' x ex false (by omega), hx0]; rfl
    | append_singleton ls k ih =>
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append,
        List.length_cons, List.length_nil, List.map_append, List.map_cons, List.map_nil,
        List.sum_append, List.sum_cons, List.sum_nil, add_zero]
      set cur := ls.foldl (fun cur k =>
        let (g1, p) := mkAnd inputs cur.1 (aW k) (bW k)
        mkXor inputs g1 cur.2 p) (gs, 0)
      have hak : aW k < inputs + cur.1.length := lt_of_lt_of_le (ha k) (Nat.add_le_add_left (extends_len ih.2.1) _)
      have hbk : bW k < inputs + cur.1.length := lt_of_lt_of_le (hb k) (Nat.add_le_add_left (extends_len ih.2.1) _)
      have hg1 := mkAnd_spec ih.1 hak hbk
      set g1 := (mkAnd inputs cur.1 (aW k) (bW k)).1
      set p := (mkAnd inputs cur.1 (aW k) (bW k)).2
      have hacc1 : cur.2 < inputs + g1.length := lt_of_lt_of_le ih.2.2.2.1 (Nat.add_le_add_left (extends_len hg1.2.1) _)
      have hg2 := mkXor_spec hg1.1 hacc1 hg1.2.2.2.1
      have hli : cur.1.length = gs.length + 5 * ls.length := ih.2.2.1
      have hlg1 : g1.length = cur.1.length + 1 := hg1.2.2.1
      have hlg2 : (mkXor inputs g1 cur.2 p).1.length = g1.length + 4 := hg2.2.2.1
      refine ⟨hg2.1, extends_trans ih.2.1 (extends_trans hg1.2.1 hg2.2.1), by change (mkXor inputs g1 cur.2 p).1.length = _; omega, hg2.2.2.2.1, ?_⟩
      intro x hx hx0
      rw [hg2.2.2.2.2 x hx, evalW_extends hg1.2.1 hx ih.2.2.2.1, ih.2.2.2.2 x hx hx0,
        hg1.2.2.2.2 x hx, evalW_extends ih.2.1 hx (ha k), evalW_extends ih.2.1 hx (hb k)]
  have h := haux (List.finRange n)
  refine ⟨h.1, h.2.1, by simpa [cDot, foldFin] using h.2.2.1,
    by simpa [cDot, foldFin] using h.2.2.2.1, fun x hx hx0 => ?_⟩
  change evalW (List.foldl _ (gs, 0) (List.finRange n)).1 x
    (List.foldl _ (gs, 0) (List.finRange n)).2 = _
  rw [h.2.2.2.2 x hx hx0, ← Fin.sum_univ_def]

private def cMatMul {n : ℕ} (inputs : ℕ) (gs : List Gate) (AW BW : Fin n → Fin n → ℕ) :
    List Gate × (Fin n → Fin n → ℕ) :=
  foldFin n (fun i cur =>
    foldFin n (fun j cur2 =>
      let (gs', w) := cDot inputs cur2.1 (fun k => AW i k) (fun k => BW k j)
      (gs', fun r c => if r = i ∧ c = j then w else cur2.2 r c)) cur) (gs, fun _ _ => 0)

private theorem cMatMul_spec {n : ℕ} {inputs : ℕ} (h0 : 0 < inputs)
    (gs : List Gate) (AW BW : Fin n → Fin n → ℕ)
    (hV : ValidG inputs gs)
    (hA : ∀ i j, AW i j < inputs + gs.length) (hB : ∀ i j, BW i j < inputs + gs.length) :
    let res := cMatMul inputs gs AW BW
    ValidG inputs res.1 ∧ Extends gs res.1 ∧
    res.1.length = gs.length + 5 * n * n * n ∧
    (∀ i j, res.2 i j < inputs + res.1.length) ∧
    ∀ (x : List Bool) (_hx : x.length = inputs) (_hx0 : x.getD 0 false = false) (A B : Mat n),
      (∀ i j, evalW gs x (AW i j) = A i j) →
      (∀ i j, evalW gs x (BW i j) = B i j) →
      ∀ i j, evalW res.1 x (res.2 i j) = matMul A B i j := by
  have hrow : ∀ (i : Fin n) (gs0 : List Gate) (M0 : Fin n → Fin n → ℕ),
      ValidG inputs gs0 → Extends gs gs0 → (∀ r c, M0 r c < inputs + gs0.length) →
      let res := foldFin n (fun j cur2 =>
        let (gs', w) := cDot inputs cur2.1 (fun k => AW i k) (fun k => BW k j)
        (gs', fun r c => if r = i ∧ c = j then w else cur2.2 r c)) (gs0, M0)
      ValidG inputs res.1 ∧ Extends gs0 res.1 ∧
      res.1.length = gs0.length + 5 * n * n ∧
      (∀ r c, res.2 r c < inputs + res.1.length) ∧
      ∀ (x : List Bool) (_hx : x.length = inputs) (_hx0 : x.getD 0 false = false) (A B : Mat n),
        (∀ r c, evalW gs x (AW r c) = A r c) →
        (∀ r c, evalW gs x (BW r c) = B r c) →
        ∀ r c, evalW res.1 x (res.2 r c) = if r = i then matMul A B i c else evalW gs0 x (M0 r c) := by
    intro i gs0 M0 hV0 hext0 hM0
    have hl_aux : ∀ (l : List (Fin n)), l.Nodup →
        let res := l.foldl (fun cur2 j =>
          let (gs', w) := cDot inputs cur2.1 (fun k => AW i k) (fun k => BW k j)
          (gs', fun r c => if r = i ∧ c = j then w else cur2.2 r c)) (gs0, M0)
        ValidG inputs res.1 ∧ Extends gs0 res.1 ∧
        res.1.length = gs0.length + 5 * n * l.length ∧
        (∀ r c, res.2 r c < inputs + res.1.length) ∧
        ∀ (x : List Bool) (_hx : x.length = inputs) (_hx0 : x.getD 0 false = false) (A B : Mat n),
          (∀ r c, evalW gs x (AW r c) = A r c) →
          (∀ r c, evalW gs x (BW r c) = B r c) →
          ∀ r c, evalW res.1 x (res.2 r c) = if r = i ∧ c ∈ l then matMul A B i c else evalW gs0 x (M0 r c) := by
      intro l hl
      induction l using List.reverseRecOn with
      | nil =>
        refine ⟨hV0, extends_refl gs0, by simp, hM0, fun x _ _ A B _ _ r c => by simp⟩
      | append_singleton ls j ih =>
        have hls : ls.Nodup := (List.nodup_append.mp hl).1
        have hprev := ih hls
        simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append,
          List.length_cons, List.length_nil]
        set cur2 := ls.foldl (fun cur2 j =>
          let (gs', w) := cDot inputs cur2.1 (fun k => AW i k) (fun k => BW k j)
          (gs', fun r c => if r = i ∧ c = j then w else cur2.2 r c)) (gs0, M0)
        have hext_gc : Extends gs cur2.1 := extends_trans hext0 hprev.2.1
        have hAk : ∀ k, AW i k < inputs + cur2.1.length := fun k => lt_of_lt_of_le (hA i k) (Nat.add_le_add_left (extends_len hext_gc) _)
        have hBk : ∀ k, BW k j < inputs + cur2.1.length := fun k => lt_of_lt_of_le (hB k j) (Nat.add_le_add_left (extends_len hext_gc) _)
        have hd := cDot_spec h0 cur2.1 (fun k => AW i k) (fun k => BW k j) hprev.1 hAk hBk
        refine ⟨hd.1, extends_trans hprev.2.1 hd.2.1, ?_, ?_, ?_⟩
        · have h1 := hprev.2.2.1; have h2 := hd.2.2.1; nlinarith
        · intro r c
          by_cases hrc : r = i ∧ c = j
          · simp only [hrc, and_self, ↓reduceIte]; exact hd.2.2.2.1
          · simp only [hrc, ↓reduceIte]
            exact lt_of_lt_of_le (hprev.2.2.2.1 r c) (Nat.add_le_add_left (extends_len hd.2.1) _)
        · intro x hx hx0 A B hAe hBe r c
          by_cases hrc : r = i ∧ c = j
          · rcases hrc with ⟨rfl, rfl⟩
            simp only [and_self, ↓reduceIte, List.mem_append, List.mem_singleton, or_true]
            rw [hd.2.2.2.2 x hx hx0]
            unfold matMul
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [evalW_extends hext_gc hx (hA r k), evalW_extends hext_gc hx (hB k c), hAe r k, hBe k c]
          · simp only [hrc, ↓reduceIte]
            rw [evalW_extends hd.2.1 hx (hprev.2.2.2.1 r c), hprev.2.2.2.2 x hx hx0 A B hAe hBe r c]
            by_cases hri : r = i
            · subst hri
              have hcj : c ≠ j := fun h => hrc ⟨rfl, h⟩
              simp [hcj]
            · simp [hri]
    have h := hl_aux (List.finRange n) (List.nodup_finRange n)
    simpa [foldFin, List.mem_finRange] using h
  have houter : ∀ (l : List (Fin n)), l.Nodup →
      let res := l.foldl (fun cur i =>
        foldFin n (fun j cur2 =>
          let (gs', w) := cDot inputs cur2.1 (fun k => AW i k) (fun k => BW k j)
          (gs', fun r c => if r = i ∧ c = j then w else cur2.2 r c)) cur) (gs, (fun _ _ : Fin n => (0 : ℕ)))
      ValidG inputs res.1 ∧ Extends gs res.1 ∧
      res.1.length = gs.length + 5 * n * n * l.length ∧
      (∀ r c, res.2 r c < inputs + res.1.length) ∧
      ∀ (x : List Bool) (_hx : x.length = inputs) (_hx0 : x.getD 0 false = false) (A B : Mat n),
        (∀ r c, evalW gs x (AW r c) = A r c) →
        (∀ r c, evalW gs x (BW r c) = B r c) →
        ∀ r ∈ l, ∀ c, evalW res.1 x (res.2 r c) = matMul A B r c := by
    intro l hl
    induction l using List.reverseRecOn with
    | nil =>
      dsimp only [List.foldl_nil]
      refine ⟨hV, extends_refl gs, by simp, fun _ _ => by omega, fun _ _ _ _ _ _ _ _ hr => by cases hr⟩
    | append_singleton ls i ih =>
      have hls : ls.Nodup := (List.nodup_append.mp hl).1
      have hprev := ih hls
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append,
        List.length_cons, List.length_nil]
      set cur := ls.foldl (fun cur i =>
        foldFin n (fun j cur2 =>
          let (gs', w) := cDot inputs cur2.1 (fun k => AW i k) (fun k => BW k j)
          (gs', fun r c => if r = i ∧ c = j then w else cur2.2 r c)) cur) (gs, (fun _ _ : Fin n => (0 : ℕ)))
      have hr := hrow i cur.1 cur.2 hprev.1 hprev.2.1 hprev.2.2.2.1
      refine ⟨hr.1, extends_trans hprev.2.1 hr.2.1, ?_, hr.2.2.2.1, ?_⟩
      · have h1 := hprev.2.2.1; have h2 := hr.2.2.1; nlinarith
      · intro x hx hx0 A B hAe hBe r hrm c
        rw [hr.2.2.2.2 x hx hx0 A B hAe hBe r c]
        by_cases hri : r = i
        · subst hri; simp
        · simp only [hri, ↓reduceIte]
          have hrls : r ∈ ls := by
            rcases List.mem_append.mp hrm with h1 | h2
            · exact h1
            · exact False.elim (hri (List.mem_singleton.mp h2))
          exact hprev.2.2.2.2 x hx hx0 A B hAe hBe r hrls c
  have h := houter (List.finRange n) (List.nodup_finRange n)
  refine ⟨h.1, h.2.1, by simpa [cMatMul, foldFin] using h.2.2.1,
    by simpa [cMatMul, foldFin] using h.2.2.2.1,
    fun x hx hx0 A B hAe hBe r c => h.2.2.2.2 x hx hx0 A B hAe hBe r (List.mem_finRange r) c⟩

private def cDeltaCols {n t d : ℕ} (inputs : ℕ)
    (enumerate : Fin (lowSet n d).card ≃ ↥(lowSet n d))
    (gs : List Gate) (cW : Fin t → Fin (lowSet n d).card → ℕ) (BW : Fin n → Fin n → ℕ) :
    List Gate × (Fin n → Fin t → Fin (lowSet n d).card → ℕ) :=
  foldFin n (fun r cur =>
    let (gs', dW) := cDeltaAll inputs enumerate cur.1 cW (fun i => BW i r)
    (gs', fun r' => if r' = r then dW else cur.2 r')) (gs, fun _ => cW)

private theorem cDeltaCols_spec {n t d : ℕ} {inputs : ℕ}
    (enumerate : Fin (lowSet n d).card ≃ ↥(lowSet n d))
    (gs : List Gate) (cW : Fin t → Fin (lowSet n d).card → ℕ) (BW : Fin n → Fin n → ℕ)
    (hV : ValidG inputs gs)
    (hc : ∀ j a, cW j a < inputs + gs.length)
    (hB : ∀ i j, BW i j < inputs + gs.length) :
    let res := cDeltaCols inputs enumerate gs cW BW
    ValidG inputs res.1 ∧ Extends gs res.1 ∧
    res.1.length ≤ gs.length + n * t * (5 * n + 4) * (lowSet n d).card ∧
    (∀ r j a, res.2 r j a < inputs + res.1.length) ∧
    ∀ (x : List Bool) (_hx : x.length = inputs) (c : Fin t → Finset (Fin n) → F) (B : Mat n),
      (∀ j a, evalW gs x (cW j a) = c j (enumerate a).val) →
      (∀ i j, evalW gs x (BW i j) = B i j) →
      ∀ r j a, evalW res.1 x (res.2 r j a) = delta d c (fun i => B i r) j (enumerate a).val := by
  have haux : ∀ (l : List (Fin n)), l.Nodup →
      let res := l.foldl (fun cur r =>
        let (gs', dW) := cDeltaAll inputs enumerate cur.1 cW (fun i => BW i r)
        (gs', fun r' => if r' = r then dW else cur.2 r')) (gs, (fun _ : Fin n => cW))
      ValidG inputs res.1 ∧ Extends gs res.1 ∧
      res.1.length ≤ gs.length + l.length * t * (5 * n + 4) * (lowSet n d).card ∧
      (∀ r j a, res.2 r j a < inputs + res.1.length) ∧
      ∀ (x : List Bool) (_hx : x.length = inputs) (c : Fin t → Finset (Fin n) → F) (B : Mat n),
        (∀ j a, evalW gs x (cW j a) = c j (enumerate a).val) →
        (∀ i j, evalW gs x (BW i j) = B i j) →
        ∀ r ∈ l, ∀ j a, evalW res.1 x (res.2 r j a) = delta d c (fun i => B i r) j (enumerate a).val := by
    intro l hl
    induction l using List.reverseRecOn with
    | nil =>
      refine ⟨hV, extends_refl gs, by simp, fun _ => hc, fun _ _ _ _ _ _ _ hr => by cases hr⟩
    | append_singleton ls r ih =>
      have hls : ls.Nodup := (List.nodup_append.mp hl).1
      have hprev := ih hls
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, List.length_append,
        List.length_cons, List.length_nil]
      set cur := ls.foldl (fun cur r =>
        let (gs', dW) := cDeltaAll inputs enumerate cur.1 cW (fun i => BW i r)
        (gs', fun r' => if r' = r then dW else cur.2 r')) (gs, (fun _ : Fin n => cW))
      have hc_c : ∀ j a, cW j a < inputs + cur.1.length :=
        fun j a => lt_of_lt_of_le (hc j a) (Nat.add_le_add_left (extends_len hprev.2.1) _)
      have hB_c : ∀ i, BW i r < inputs + cur.1.length :=
        fun i => lt_of_lt_of_le (hB i r) (Nat.add_le_add_left (extends_len hprev.2.1) _)
      have hd := cDeltaAll_spec enumerate cur.1 cW (fun i => BW i r) hprev.1 hc_c hB_c
      refine ⟨hd.1, extends_trans hprev.2.1 hd.2.1, ?_, ?_, ?_⟩
      · have h1 := hprev.2.2.1; have h2 := hd.2.2.1; nlinarith
      · intro r' j a
        by_cases hr' : r' = r
        · subst hr'; simpa using hd.2.2.2.1 j a
        · simp only [hr', ↓reduceIte]
          exact lt_of_lt_of_le (hprev.2.2.2.1 r' j a) (Nat.add_le_add_left (extends_len hd.2.1) _)
      · intro x hx c B hce hBe r' hr' j a
        by_cases heq : r' = r
        · subst heq
          simp only [↓reduceIte]
          exact hd.2.2.2.2 x hx c (fun i => B i r')
            (fun j' a' => by rw [evalW_extends hprev.2.1 hx (hc j' a'), hce j' a'])
            (fun i => by rw [evalW_extends hprev.2.1 hx (hB i r'), hBe i r']) j a
        · simp only [heq, ↓reduceIte]
          rw [evalW_extends hd.2.1 hx (hprev.2.2.2.1 r' j a)]
          have hrls : r' ∈ ls := by
            rcases List.mem_append.mp hr' with h1 | h2
            · exact h1
            · exact False.elim (heq (List.mem_singleton.mp h2))
          exact hprev.2.2.2.2 x hx c B hce hBe r' hrls j a
  have h := haux (List.finRange n) (List.nodup_finRange n)
  refine ⟨h.1, h.2.1, by simpa [cDeltaCols, foldFin] using h.2.2.1,
    by simpa [cDeltaCols, foldFin] using h.2.2.2.1,
    fun x hx c B hce hBe r j a => h.2.2.2.2 x hx c B hce hBe r (List.mem_finRange r) j a⟩

private def cDescentStep {n t d : ℕ} (inputs : ℕ) (k : ℕ)
    (enumerate : Fin (lowSet n d).card ≃ ↥(lowSet n d))
    (gs : List Gate) (cW : Fin t → Fin (lowSet n d).card → ℕ) (BW : Fin n → Fin n → ℕ) :
    List Gate × (Fin n → Fin n → ℕ) :=
  let (gs1, D) := cDeltaCols inputs enumerate gs cW BW
  let rowsW : List (Fin n → ℕ) :=
    (List.finRange t).flatMap fun j =>
      ((List.finRange (lowSet n d).card).filter fun a => (enumerate a).val.card = k).map fun a =>
        fun r : Fin n => D r j a
  let (gs2, RW) := cRREF inputs gs1 rowsW
  let (gs3, KW) := cKerProj inputs gs2 RW
  cMatMul inputs gs3 BW KW

private theorem flatMap_filter_len_le {n t d : ℕ} (k : ℕ)
    (enumerate : Fin (lowSet n d).card ≃ ↥(lowSet n d)) {α : Type}
    (f : Fin t → Fin (lowSet n d).card → α) :
    ((List.finRange t).flatMap fun j =>
      ((List.finRange (lowSet n d).card).filter fun a => (enumerate a).val.card = k).map fun a =>
        f j a).length ≤ t * (lowSet n d).card := by
  have haux : ∀ (l : List (Fin t)),
      (l.flatMap fun j =>
        ((List.finRange (lowSet n d).card).filter fun a => (enumerate a).val.card = k).map fun a =>
          f j a).length ≤ l.length * (lowSet n d).card := by
    intro l
    induction l with
    | nil => simp
    | cons j js ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons]
      have hfilt : ((List.finRange (lowSet n d).card).filter fun a => (enumerate a).val.card = k).length ≤
          (lowSet n d).card := by
        calc _ ≤ (List.finRange (lowSet n d).card).length := List.length_filter_le _ _
          _ = (lowSet n d).card := List.length_finRange
      nlinarith
  have h := haux (List.finRange t)
  simpa using h

private theorem cDescentStep_spec {n t d : ℕ} {inputs : ℕ} (h0 : 0 < inputs) (k : ℕ)
    (enumerate : Fin (lowSet n d).card ≃ ↥(lowSet n d))
    (gs : List Gate) (cW : Fin t → Fin (lowSet n d).card → ℕ) (BW : Fin n → Fin n → ℕ)
    (hV : ValidG inputs gs)
    (hc : ∀ j a, cW j a < inputs + gs.length)
    (hB : ∀ i j, BW i j < inputs + gs.length) :
    let res := cDescentStep inputs k enumerate gs cW BW
    ValidG inputs res.1 ∧ Extends gs res.1 ∧
    res.1.length ≤ gs.length +
      n * t * (5 * n + 4) * (lowSet n d).card +
      (t * (lowSet n d).card) * (n * (3 + 11 * n)) +
      5 * n * n * n + n + 5 * n * n * n ∧
    (∀ i j, res.2 i j < inputs + res.1.length) ∧
    ∀ (x : List Bool) (_hx : x.length = inputs) (_hx0 : x.getD 0 false = false)
      (c : Fin t → Finset (Fin n) → F) (B : Mat n),
      (∀ j a, evalW gs x (cW j a) = c j (enumerate a).val) →
      (∀ i j, evalW gs x (BW i j) = B i j) →
      ∀ i j, evalW res.1 x (res.2 i j) = descentStep d k enumerate c B i j := by
  unfold cDescentStep
  have h1 := cDeltaCols_spec enumerate gs cW BW hV hc hB
  set gs1 := (cDeltaCols inputs enumerate gs cW BW).1
  set D := (cDeltaCols inputs enumerate gs cW BW).2
  set rowsW : List (Fin n → ℕ) :=
    (List.finRange t).flatMap fun j =>
      ((List.finRange (lowSet n d).card).filter fun a => (enumerate a).val.card = k).map fun a =>
        fun r : Fin n => D r j a
  have hrows_wf : ∀ wW ∈ rowsW, ∀ r, wW r < inputs + gs1.length := by
    intro wW hw r
    simp only [rowsW, List.mem_flatMap, List.mem_map, List.mem_filter, List.mem_finRange,
      true_and, decide_eq_true_eq] at hw
    obtain ⟨j, a, _, rfl⟩ := hw
    exact h1.2.2.2.1 r j a
  have h2 := cRREF_spec h0 gs1 rowsW h1.1 hrows_wf
  set gs2 := (cRREF inputs gs1 rowsW).1
  set RW := (cRREF inputs gs1 rowsW).2
  have h3 := cKerProj_spec gs2 RW h2.1 h2.2.2.2.1
  set gs3 := (cKerProj inputs gs2 RW).1
  set KW := (cKerProj inputs gs2 RW).2
  have hext03 : Extends gs gs3 := extends_trans (extends_trans h1.2.1 h2.2.1) h3.2.1
  have hB3 : ∀ i j, BW i j < inputs + gs3.length :=
    fun i j => lt_of_lt_of_le (hB i j) (Nat.add_le_add_left (extends_len hext03) _)
  have h4 := cMatMul_spec h0 gs3 BW KW h3.1 hB3 h3.2.2.2.1
  refine ⟨h4.1, extends_trans hext03 h4.2.1, ?_, h4.2.2.2.1, ?_⟩
  · have hlen_rows : rowsW.length ≤ t * (lowSet n d).card :=
      flatMap_filter_len_le k enumerate (fun j a r => D r j a)
    have ha : gs1.length ≤ gs.length + n * t * (5 * n + 4) * (lowSet n d).card := h1.2.2.1
    have hb : gs2.length ≤ gs1.length + rowsW.length * (n * (3 + 11 * n)) + 5 * n * n * n := h2.2.2.1
    have hc' : gs3.length = gs2.length + n := h3.2.2.1
    have hd' : (cMatMul inputs gs3 BW KW).1.length = gs3.length + 5 * n * n * n := h4.2.2.1
    have hmul : rowsW.length * (n * (3 + 11 * n)) ≤ (t * (lowSet n d).card) * (n * (3 + 11 * n)) :=
      Nat.mul_le_mul_right _ hlen_rows
    change (cMatMul inputs gs3 BW KW).1.length ≤ _
    linarith
  · intro x hx hx0 c B hce hBe i j
    set rows : List (Vec n) :=
      (List.finRange t).flatMap fun j =>
        ((List.finRange (lowSet n d).card).filter fun a => (enumerate a).val.card = k).map fun a =>
          fun r : Fin n => delta d c (fun i => B i r) j (enumerate a).val
    have hrel : List.Forall₂ (fun wW row => ∀ r, evalW gs1 x (wW r) = row r) rowsW rows := by
      have hflat : ∀ (lt : List (Fin t)),
          List.Forall₂ (fun wW row => ∀ r, evalW gs1 x (wW r) = row r)
            (lt.flatMap fun j =>
              ((List.finRange (lowSet n d).card).filter fun a => (enumerate a).val.card = k).map fun a =>
                fun r : Fin n => D r j a)
            (lt.flatMap fun j =>
              ((List.finRange (lowSet n d).card).filter fun a => (enumerate a).val.card = k).map fun a =>
                fun r : Fin n => delta d c (fun i => B i r) j (enumerate a).val) := by
        intro lt
        induction lt with
        | nil => simp
        | cons j js ihj =>
          simp only [List.flatMap_cons]
          exact forall2_append' (by rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]; intro a _ r; exact h1.2.2.2.2 x hx c B hce hBe r j a) ihj
      exact hflat (List.finRange t)
    exact h4.2.2.2.2 x hx hx0 B (kerProj (rref rows))
      (fun r' c' => by rw [evalW_extends hext03 hx (hB r' c'), hBe r' c'])
      (h3.2.2.2.2 x hx (rref rows) (h2.2.2.2.2 x hx hx0 rows hrel)) i j

private def cDescentDown {n t d : ℕ} (inputs : ℕ)
    (enumerate : Fin (lowSet n d).card ≃ ↥(lowSet n d))
    (cW : Fin t → Fin (lowSet n d).card → ℕ) :
    ℕ → List Gate → (Fin n → Fin n → ℕ) → List Gate × (Fin n → Fin n → ℕ)
  | 0, gs, BW => (gs, BW)
  | k + 1, gs, BW =>
    let (gs', BW') := cDescentStep inputs (k + 1) enumerate gs cW BW
    cDescentDown inputs enumerate cW k gs' BW'

private theorem cDescentDown_spec {n t d : ℕ} {inputs : ℕ} (h0 : 0 < inputs)
    (enumerate : Fin (lowSet n d).card ≃ ↥(lowSet n d))
    (cW : Fin t → Fin (lowSet n d).card → ℕ) :
    ∀ (k : ℕ) (gs : List Gate) (BW : Fin n → Fin n → ℕ),
      ValidG inputs gs →
      (∀ j a, cW j a < inputs + gs.length) →
      (∀ i j, BW i j < inputs + gs.length) →
      let res := cDescentDown inputs enumerate cW k gs BW
      ValidG inputs res.1 ∧ Extends gs res.1 ∧
      res.1.length ≤ gs.length + k * (
        n * t * (5 * n + 4) * (lowSet n d).card +
        (t * (lowSet n d).card) * (n * (3 + 11 * n)) +
        5 * n * n * n + n + 5 * n * n * n) ∧
      (∀ i j, res.2 i j < inputs + res.1.length) ∧
      ∀ (x : List Bool) (_hx : x.length = inputs) (_hx0 : x.getD 0 false = false)
        (c : Fin t → Finset (Fin n) → F) (B : Mat n),
        (∀ j a, evalW gs x (cW j a) = c j (enumerate a).val) →
        (∀ i j, evalW gs x (BW i j) = B i j) →
        ∀ i j, evalW res.1 x (res.2 i j) = descentDown d enumerate c k B i j := by
  intro k
  induction k with
  | zero =>
    intro gs BW hV _ hB
    dsimp only [cDescentDown]
    exact ⟨hV, extends_refl gs, by simp, hB, fun x _ _ c B _ hBe i j => hBe i j⟩
  | succ k' ih =>
    intro gs BW hV hc hB
    have h1 := cDescentStep_spec h0 (k' + 1) enumerate gs cW BW hV hc hB
    set gs1 := (cDescentStep inputs (k' + 1) enumerate gs cW BW).1
    set BW1 := (cDescentStep inputs (k' + 1) enumerate gs cW BW).2
    have hc1 : ∀ j a, cW j a < inputs + gs1.length :=
      fun j a => lt_of_lt_of_le (hc j a) (Nat.add_le_add_left (extends_len h1.2.1) _)
    have h2 := ih gs1 BW1 h1.1 hc1 h1.2.2.2.1
    dsimp only [cDescentDown]
    refine ⟨h2.1, extends_trans h1.2.1 h2.2.1, ?_, h2.2.2.2.1, ?_⟩
    · have ha := h1.2.2.1
      have hb := h2.2.2.1
      nlinarith
    · intro x hx hx0 c B hce hBe i j
      exact h2.2.2.2.2 x hx hx0 c (descentStep d (k' + 1) enumerate c B)
        (fun j' a' => by rw [evalW_extends h1.2.1 hx (hc j' a'), hce j' a'])
        (h1.2.2.2.2 x hx hx0 c B hce hBe) i j

private theorem bits_len_and_getD {n t d : ℕ}
    (enumerate : Fin (lowSet n d).card ≃ ↥(lowSet n d))
    (f : Vec n → (Fin t → F)) :
    let bits := [false] ++ (List.ofFn (fun component : Fin t =>
      List.ofFn (fun a : Fin (lowSet n d).card =>
        decide (f (fun i => if i ∈ (enumerate a).val then 1 else 0) component ≠ 0)))).flatten
    bits.length = 1 + t * (lowSet n d).card ∧
    bits.getD 0 false = false ∧
    ∀ (j : Fin t) (a : Fin (lowSet n d).card),
      b2z (bits.getD (1 + j.val * (lowSet n d).card + a.val) false) = f (ind (enumerate a).val) j := by
  dsimp only
  let rowF : Fin t → List Bool := fun component =>
    List.ofFn (fun a : Fin (lowSet n d).card =>
      decide (f (fun i => if i ∈ (enumerate a).val then 1 else 0) component ≠ 0))
  have hrow_len : ∀ j : Fin t, (rowF j).length = (lowSet n d).card := fun j => by simp [rowF]
  have hflat_len : (List.ofFn rowF).flatten.length = t * (lowSet n d).card := by
    rw [List.length_flatten, List.map_ofFn]
    have hconst : List.ofFn (List.length ∘ rowF) = List.replicate t (lowSet n d).card := by
      apply List.ext_getElem
      · simp
      · intro i hi1 hi2; simp [hrow_len]
    rw [hconst, List.sum_replicate, smul_eq_mul]
  have hflat_get : ∀ (j : Fin t) (a : Fin (lowSet n d).card),
      ((List.ofFn rowF).flatten).getD (j.val * (lowSet n d).card + a.val) false =
        decide (f (ind (enumerate a).val) j ≠ 0) := by
    have haux : ∀ (k : ℕ) (g : Fin k → List Bool), (∀ i, (g i).length = (lowSet n d).card) →
        ∀ (j : Fin k) (a : Fin (lowSet n d).card),
          ((List.ofFn g).flatten).getD (j.val * (lowSet n d).card + a.val) false = (g j).getD a.val false := by
      intro k
      induction k with
      | zero => intro _ _ j; exact Fin.elim0 j
      | succ k' ih =>
        intro g hg j a
        rw [List.ofFn_succ, List.flatten_cons]
        refine Fin.cases ?_ ?_ j
        · simp only [Fin.val_zero, zero_mul, zero_add]
          rw [getD_append_left' _ _ _ (by rw [hg 0]; exact a.isLt)]
        · intro j'
          simp only [Fin.val_succ, List.getD_eq_getElem?_getD]
          have hge : (g 0).length ≤ (j'.val + 1) * (lowSet n d).card + a.val := by rw [hg 0]; nlinarith
          rw [List.getElem?_append_right hge, hg 0]
          have hsub : (j'.val + 1) * (lowSet n d).card + a.val - (lowSet n d).card =
              j'.val * (lowSet n d).card + a.val := by
            rw [add_mul, one_mul]; omega
          rw [hsub]
          have hrec := ih (fun i => g i.succ) (fun i => hg i.succ) j' a
          simpa [List.getD_eq_getElem?_getD] using hrec
    intro j a
    rw [haux t rowF hrow_len j a, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [hrow_len]; exact a.isLt)]
    simp [rowF]; rfl
  refine ⟨by change ([false] ++ (List.ofFn rowF).flatten).length = _; simp only [List.length_append, List.length_cons, List.length_nil, hflat_len], by simp, fun j a => ?_⟩
  have hidx : 1 + j.val * (lowSet n d).card + a.val = (j.val * (lowSet n d).card + a.val) + 1 := by omega
  rw [hidx]
  change b2z (([false] ++ (List.ofFn rowF).flatten).getD ((j.val * (lowSet n d).card + a.val) + 1) false) = _
  simp only [List.singleton_append, List.getD_cons_succ, hflat_get j a]
  exact b2z_decide_ne_zero _

private theorem size_bound_arith (n t B : ℕ) (hB : 1 ≤ B) :
    1 + 4 * t * n * B +
      min d n * (n * t * (5 * n + 4) * B + (t * B) * (n * (3 + 11 * n)) +
        5 * n * n * n + n + 5 * n * n * n) +
      n * (n * (3 + 11 * n)) + 5 * n * n * n +
      n * t * (5 * n + 4) * B ≤
      2 ^ 20 * (n + t + 2) ^ 9 * B := by
  have hD : min d n ≤ n := min_le_right d n
  set S := n + t + 2
  have hn : n ≤ S := by omega
  have ht : t ≤ S := by omega
  have hS2 : 2 ≤ S := by omega
  have hS1 : 1 ≤ S := by omega
  have hpow4 : S ^ 4 ≤ S ^ 9 := Nat.pow_le_pow_right hS1 (by omega)
  have h1 : 1 ≤ S ^ 4 * B := by
    have : 1 ≤ S ^ 4 := Nat.one_le_pow 4 S hS1
    nlinarith
  have h2 : 4 * t * n * B ≤ 4 * S ^ 4 * B := by
    have : t * n ≤ S * S := Nat.mul_le_mul ht hn
    have : S * S ≤ S ^ 4 := by
      calc S * S = S ^ 2 := by ring
        _ ≤ S ^ 4 := Nat.pow_le_pow_right hS1 (by omega)
    nlinarith
  have hstep_le : n * t * (5 * n + 4) * B + (t * B) * (n * (3 + 11 * n)) +
      5 * n * n * n + n + 5 * n * n * n ≤ 40 * S ^ 3 * B := by
    have ha : n * t * (5 * n + 4) ≤ 9 * S ^ 3 := by
      have : 5 * n + 4 ≤ 9 * S := by omega
      have hnt : n * t ≤ S * S := Nat.mul_le_mul hn ht
      have hmul := Nat.mul_le_mul hnt this
      nlinarith
    have hb : t * (n * (3 + 11 * n)) ≤ 14 * S ^ 3 := by
      have : 3 + 11 * n ≤ 14 * S := by omega
      have hnt : t * n ≤ S * S := Nat.mul_le_mul ht hn
      have hmul := Nat.mul_le_mul hnt this
      nlinarith
    have hc : 5 * n * n * n + n + 5 * n * n * n ≤ 11 * S ^ 3 * B := by
      have hn3 : n * n * n ≤ S ^ 3 := by
        have h1' : n * n ≤ S * S := Nat.mul_le_mul hn hn
        have h2' : n * n * n ≤ S * S * S := Nat.mul_le_mul h1' hn
        nlinarith
      have hn1 : n ≤ S ^ 3 := by
        calc n ≤ S := hn
          _ = S ^ 1 := by ring
          _ ≤ S ^ 3 := Nat.pow_le_pow_right hS1 (by omega)
      have hsum : 5 * n * n * n + n + 5 * n * n * n ≤ 11 * S ^ 3 := by linarith
      calc 5 * n * n * n + n + 5 * n * n * n ≤ 11 * S ^ 3 := hsum
        _ = 11 * S ^ 3 * 1 := by ring
        _ ≤ 11 * S ^ 3 * B := Nat.mul_le_mul_left _ hB
    have haB : n * t * (5 * n + 4) * B ≤ 9 * S ^ 3 * B := Nat.mul_le_mul_right B ha
    have hbB : (t * B) * (n * (3 + 11 * n)) ≤ 14 * S ^ 3 * B := by
      have : (t * B) * (n * (3 + 11 * n)) = t * (n * (3 + 11 * n)) * B := by ring
      rw [this]
      exact Nat.mul_le_mul_right B hb
    nlinarith
  have h3 : min d n * (n * t * (5 * n + 4) * B + (t * B) * (n * (3 + 11 * n)) +
      5 * n * n * n + n + 5 * n * n * n) ≤ 40 * S ^ 4 * B := by
    calc _ ≤ n * (40 * S ^ 3 * B) := Nat.mul_le_mul hD hstep_le
      _ ≤ S * (40 * S ^ 3 * B) := Nat.mul_le_mul_right _ hn
      _ = 40 * S ^ 4 * B := by ring
  have h4 : n * (n * (3 + 11 * n)) + 5 * n * n * n ≤ 19 * S ^ 4 * B := by
    have hlin : 3 + 11 * n ≤ 14 * S := by omega
    have hnn : n * n ≤ S * S := Nat.mul_le_mul hn hn
    have h1' : n * (n * (3 + 11 * n)) ≤ 14 * S ^ 3 := by
      have := Nat.mul_le_mul hnn hlin
      nlinarith
    have h2' : n * n * n ≤ S ^ 3 := by
      have := Nat.mul_le_mul hnn hn
      nlinarith
    have hS34 : S ^ 3 ≤ S ^ 4 := Nat.pow_le_pow_right hS1 (by omega)
    have hsum : n * (n * (3 + 11 * n)) + 5 * n * n * n ≤ 19 * S ^ 4 := by nlinarith
    calc _ ≤ 19 * S ^ 4 := hsum
      _ = 19 * S ^ 4 * 1 := by ring
      _ ≤ 19 * S ^ 4 * B := Nat.mul_le_mul_left _ hB
  have h5 : n * t * (5 * n + 4) * B ≤ 9 * S ^ 4 * B := by
    have ha : 5 * n + 4 ≤ 9 * S := by omega
    have hnt : n * t ≤ S * S := Nat.mul_le_mul hn ht
    have h3' : n * t * (5 * n + 4) ≤ 9 * S ^ 3 := by
      have := Nat.mul_le_mul hnt ha
      nlinarith
    have hS34 : S ^ 3 ≤ S ^ 4 := Nat.pow_le_pow_right hS1 (by omega)
    have h4' : n * t * (5 * n + 4) ≤ 9 * S ^ 4 := by nlinarith
    exact Nat.mul_le_mul_right B h4'
  have htot : 1 + 4 * t * n * B +
      min d n * (n * t * (5 * n + 4) * B + (t * B) * (n * (3 + 11 * n)) +
        5 * n * n * n + n + 5 * n * n * n) +
      n * (n * (3 + 11 * n)) + 5 * n * n * n +
      n * t * (5 * n + 4) * B ≤ 73 * S ^ 4 * B := by linarith
  have hbig : 73 * S ^ 4 * B ≤ 2 ^ 20 * S ^ 9 * B := by
    have h73 : 73 * S ^ 4 ≤ 2 ^ 20 * S ^ 9 := by
      calc 73 * S ^ 4 ≤ 2 ^ 20 * S ^ 4 := Nat.mul_le_mul_right _ (by norm_num)
        _ ≤ 2 ^ 20 * S ^ 9 := Nat.mul_le_mul_left _ hpow4
    exact Nat.mul_le_mul_right B h73
  exact le_trans htot hbig

private theorem solve_629 :
    ∀ (n t d : ℕ),
      let F := ZMod 2
      let X := Fin n → F
      let Y := Fin t → F
      let low := Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ d)
      ∀ enumerate : Fin low.card ≃ ↥low,
        let inputs := 1+t*low.card
        ∃ (C : PEqualNP.CircuitLowerBounds.Circuit)
          (proj : Fin n → Fin n → Fin (inputs+C.size))
          (offset : Fin t → Fin n → Fin (inputs+C.size)),
          PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs C ∧
          C.size ≤ 2^20 * (n+t+2)^9 * low.card ∧
          ∀ f : X → Y,
            (∀ j : Fin t, ∃ c : Finset (Fin n) → F, ∀ x : X,
              f x j = ∑ S ∈ low, c S * ∏ i ∈ S, x i) →
            let bits := [false] ++ (List.ofFn (fun component : Fin t =>
              List.ofFn (fun a : Fin low.card =>
                decide (f (fun i => if i ∈ (enumerate a).val then 1 else 0) component ≠ 0)))).flatten
            let bit := fun w : Fin (inputs+C.size) => if (C.wires bits).getD w.val false then (1:F) else 0
            let P := fun (v : X) (row : Fin n) => ∑ i : Fin n, bit (proj row i) * v i
            let L := fun (direction : X) (coord : Fin t) => ∑ i : Fin n, bit (offset coord i) * direction i
            (∀ z : X, P (P z) = P z) ∧ ∀ (v : X) (a : Y),
              (∀ x : X, f (x+v) = f x + a) ↔ P v = v ∧ L v = a := by
  intro n t d F_ X Y low enumerate inputs
  have hlow_eq : low = lowSet n d := rfl
  have h0 : 0 < inputs := by simp [inputs]
  have hV0 : ValidG inputs [] := ⟨fun _ h => (by cases h), fun _ hj => absurd hj (Nat.not_lt_zero _)⟩

  have hnot0 := mkNot_spec hV0 (a := 0) (by simpa using h0)
  set gs0 := (mkNot inputs [] 0).1
  set w1 := (mkNot inputs [] 0).2

  let inW : Fin t → Fin (lowSet n d).card → ℕ := fun j a => 1 + j.val * (lowSet n d).card + a.val
  have hinW : ∀ j a, inW j a < inputs + gs0.length := by
    intro j a
    have hj : j.val + 1 ≤ t := j.isLt
    have hmul : j.val * (lowSet n d).card + (lowSet n d).card ≤ t * (lowSet n d).card := by
      calc j.val * (lowSet n d).card + (lowSet n d).card = (j.val + 1) * (lowSet n d).card := by ring
        _ ≤ t * (lowSet n d).card := Nat.mul_le_mul_right _ hj
    have ha : a.val < (lowSet n d).card := a.isLt
    change 1 + j.val * (lowSet n d).card + a.val < 1 + t * (lowSet n d).card + gs0.length
    omega
  have hmob := cMobiusAll_spec enumerate gs0 inW hnot0.1 hinW
  set gs1 := (cMobiusAll inputs enumerate gs0 inW).1
  set cW := (cMobiusAll inputs enumerate gs0 inW).2

  let idW : Fin n → Fin n → ℕ := fun i j => if i = j then w1 else 0
  have hidW : ∀ i j, idW i j < inputs + gs1.length := by
    intro i j
    dsimp only [idW]
    split_ifs
    · exact lt_of_lt_of_le hnot0.2.2.2.1 (Nat.add_le_add_left (extends_len hmob.2.1) _)
    · omega
  have hdesc := cDescentDown_spec h0 enumerate cW (min d n) gs1 idW hmob.1 hmob.2.2.2.1 hidW
  set gs2 := (cDescentDown inputs enumerate cW (min d n) gs1 idW).1
  set B0W := (cDescentDown inputs enumerate cW (min d n) gs1 idW).2

  let rowsBT : List (Fin n → ℕ) := List.ofFn (fun i j => B0W j i)
  have hrowsBT : ∀ wW ∈ rowsBT, ∀ j, wW j < inputs + gs2.length := by
    intro wW hw j
    simp only [rowsBT, List.mem_ofFn] at hw
    obtain ⟨i, rfl⟩ := hw
    exact hdesc.2.2.2.1 j i
  have hQ := cRREF_spec h0 gs2 rowsBT hdesc.1 hrowsBT
  set gs3 := (cRREF inputs gs2 rowsBT).1
  set QW := (cRREF inputs gs2 rowsBT).2
  let PW : Fin n → Fin n → ℕ := fun i j => QW j i
  have hPW : ∀ i j, PW i j < inputs + gs3.length := fun i j => hQ.2.2.2.1 j i

  have hext13 : Extends gs1 gs3 := extends_trans hdesc.2.1 hQ.2.1
  have hcW3 : ∀ j a, cW j a < inputs + gs3.length :=
    fun j a => lt_of_lt_of_le (hmob.2.2.2.1 j a) (Nat.add_le_add_left (extends_len hext13) _)
  have hDL := cDeltaCols_spec enumerate gs3 cW PW hQ.1 hcW3 hPW
  set gs4 := (cDeltaCols inputs enumerate gs3 cW PW).1
  set DW := (cDeltaCols inputs enumerate gs3 cW PW).2
  let emptyIdx : Fin (lowSet n d).card := enumerate.symm ⟨∅, empty_mem_lowSet n d⟩
  let C : Circuit := ⟨gs4, 0⟩
  have hPW4 : ∀ i j, PW i j < inputs + C.size :=
    fun i j => lt_of_lt_of_le (hPW i j) (Nat.add_le_add_left (extends_len hDL.2.1) _)
  let proj : Fin n → Fin n → Fin (inputs + C.size) := fun r c => ⟨PW r c, hPW4 r c⟩
  let offset : Fin t → Fin n → Fin (inputs + C.size) := fun j i => ⟨DW i j emptyIdx, hDL.2.2.2.1 i j emptyIdx⟩
  refine ⟨C, proj, offset, ?_, ?_, ?_, ?_⟩
  ·
    exact hDL.1.1
  ·
    exact hDL.1.2
  ·
    change gs4.length ≤ 2 ^ 20 * (n + t + 2) ^ 9 * (lowSet n d).card
    have hlen0 : gs0.length = 1 := by simpa using hnot0.2.2.1
    have hlen1 := hmob.2.2.1
    have hlen2 := hdesc.2.2.1
    have hlen3 := hQ.2.2.1
    have hlen4 := hDL.2.2.1
    have hrows_len : rowsBT.length = n := by simp [rowsBT]
    rw [hrows_len] at hlen3
    have hB1 : 1 ≤ (lowSet n d).card := lowSet_card_pos n d
    have harith := size_bound_arith (d := d) n t (lowSet n d).card hB1
    linarith
  ·
    intro f hf_poly
    dsimp only
    set bits := [false] ++ (List.ofFn (fun component : Fin t =>
      List.ofFn (fun a : Fin low.card =>
        decide (f (fun i => if i ∈ (enumerate a).val then 1 else 0) component ≠ 0)))).flatten
    have hbits := bits_len_and_getD enumerate f
    have hbits_len : bits.length = inputs := hbits.1
    have hbits_0 : bits.getD 0 false = false := hbits.2.1
    have hbits_in : ∀ j a, evalW gs0 bits (inW j a) = f (ind (enumerate a).val) j := by
      intro j a
      have hin0 : inW j a < inputs + ([] : List Gate).length := by
        have hj : j.val + 1 ≤ t := j.isLt
        have hmul : j.val * (lowSet n d).card + (lowSet n d).card ≤ t * (lowSet n d).card := by
          calc j.val * (lowSet n d).card + (lowSet n d).card = (j.val + 1) * (lowSet n d).card := by ring
            _ ≤ t * (lowSet n d).card := Nat.mul_le_mul_right _ hj
        have ha : a.val < (lowSet n d).card := a.isLt
        change 1 + j.val * (lowSet n d).card + a.val < 1 + t * (lowSet n d).card + ([] : List Gate).length
        simp only [List.length_nil, Nat.add_zero]
        omega
      rw [evalW_extends hnot0.2.1 hbits_len hin0]
      unfold evalW wiresG
      simp only [List.foldl_nil]
      exact hbits.2.2 j a
    have hw1_eval : evalW gs0 bits w1 = 1 := by
      rw [hnot0.2.2.2.2 bits hbits_len]
      unfold evalW wiresG
      simp only [List.foldl_nil, hbits_0]
      decide
    set c : Fin t → Finset (Fin n) → F := fun j => mobius (fun T => f (ind T) j)
    have hcW_eval : ∀ j a, evalW gs1 bits (cW j a) = c j (enumerate a).val :=
      hmob.2.2.2.2 bits hbits_len (fun j T => f (ind T) j) hbits_in
    have hidW_eval : ∀ i j, evalW gs1 bits (idW i j) = matId n i j := by
      intro i j
      dsimp only [idW, matId]
      split_ifs
      · rw [evalW_extends hmob.2.1 hbits_len hnot0.2.2.2.1, hw1_eval]
      · have hzero : evalW gs1 bits 0 = 0 := by
          unfold evalW
          obtain ⟨ex, hex⟩ := wiresG_prefix gs1 bits
          rw [hex, getD_append_left' bits ex false (by omega), hbits_0]
          rfl
        exact hzero
    set B0 : Mat n := descentDown d enumerate c (min d n) (matId n)
    have hB0_eval : ∀ i j, evalW gs2 bits (B0W i j) = B0 i j :=
      hdesc.2.2.2.2 bits hbits_len hbits_0 c (matId n) hcW_eval hidW_eval
    have hrelBT : List.Forall₂ (fun wW r => ∀ j, evalW gs2 bits (wW j) = r j)
        rowsBT (List.ofFn (matTrans B0)) := by
      dsimp only [rowsBT]
      have hof1 : List.ofFn (fun i j => B0W j i) = (List.finRange n).map (fun i j => B0W j i) :=
        List.ext_getElem (by simp) (by intro i h1 h2; simp)
      have hof2 : List.ofFn (matTrans B0) = (List.finRange n).map (matTrans B0) :=
        List.ext_getElem (by simp) (by intro i h1 h2; simp)
      rw [hof1, hof2, List.forall₂_map_left_iff,
        List.forall₂_map_right_iff, List.forall₂_same]
      intro i _ j
      exact hB0_eval j i
    set Q : Mat n := rref (List.ofFn (matTrans B0))
    have hQ_eval : ∀ i j, evalW gs3 bits (QW i j) = Q i j :=
      hQ.2.2.2.2 bits hbits_len hbits_0 (List.ofFn (matTrans B0)) hrelBT
    set P_mat : Mat n := matTrans Q
    have hP_eval3 : ∀ i j, evalW gs3 bits (PW i j) = P_mat i j := fun i j => hQ_eval j i
    have hDL_eval : ∀ r j a, evalW gs4 bits (DW r j a) = delta d c (fun row => P_mat row r) j (enumerate a).val :=
      hDL.2.2.2.2 bits hbits_len c P_mat
        (fun j a => by rw [evalW_extends hext13 hbits_len (hmob.2.2.2.1 j a)]; exact hcW_eval j a)
        hP_eval3
    have hbit_P : ∀ row i : Fin n,
        (if (C.wires bits).getD (proj row i).val false then (1 : F) else 0) = P_mat row i := by
      intro row i
      change evalW gs4 bits (PW row i) = P_mat row i
      rw [evalW_extends hDL.2.1 hbits_len (hPW row i), hP_eval3 row i]
    have hbit_L : ∀ (coord : Fin t) (i : Fin n),
        (if (C.wires bits).getD (offset coord i).val false then (1 : F) else 0) =
          delta d c (fun row => P_mat row i) coord ∅ := by
      intro coord i
      change evalW gs4 bits (DW i coord emptyIdx) = delta d c (fun row => P_mat row i) coord ∅
      rw [hDL_eval i coord emptyIdx]
      have hemp : (enumerate emptyIdx).val = ∅ := by simp [emptyIdx]
      rw [hemp]
    simp only [hbit_P, hbit_L]
    exact pure_algo_spec enumerate f hf_poly

end PEqualNP.Outside.L_lib_629_aux

theorem PEqualNP.Outside.L_lib_629 :
    ∀ (n t d : ℕ),
      let F := ZMod 2
      let X := Fin n → F
      let Y := Fin t → F
      let low := Finset.univ.filter (fun S : Finset (Fin n) => S.card ≤ d)
      ∀ enumerate : Fin low.card ≃ ↥low,
        let inputs := 1+t*low.card
        ∃ (C : PEqualNP.CircuitLowerBounds.Circuit)
          (proj : Fin n → Fin n → Fin (inputs+C.size))
          (offset : Fin t → Fin n → Fin (inputs+C.size)),
          PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack inputs C ∧
          C.size ≤ 2^20 * (n+t+2)^9 * low.card ∧
          ∀ f : X → Y,
            (∀ j : Fin t, ∃ c : Finset (Fin n) → F, ∀ x : X,
              f x j = ∑ S ∈ low, c S * ∏ i ∈ S, x i) →
            let bits := [false] ++ (List.ofFn (fun component : Fin t =>
              List.ofFn (fun a : Fin low.card =>
                decide (f (fun i => if i ∈ (enumerate a).val then 1 else 0) component ≠ 0)))).flatten
            let bit := fun w : Fin (inputs+C.size) => if (C.wires bits).getD w.val false then (1:F) else 0
            let P := fun (v : X) (row : Fin n) => ∑ i : Fin n, bit (proj row i) * v i
            let L := fun (direction : X) (coord : Fin t) => ∑ i : Fin n, bit (offset coord i) * direction i
            (∀ z : X, P (P z) = P z) ∧ ∀ (v : X) (a : Y),
              (∀ x : X, f (x+v) = f x + a) ↔ P v = v ∧ L v = a :=
  PEqualNP.Outside.L_lib_629_aux.solve_629
